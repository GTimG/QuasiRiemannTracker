"""Parallel isolated rebuild of a target's whole local dependency closure.

Same contract as verify.py, with these differences:
  * the live development directory is removed from LEAN_PATH, so every local
    import can only resolve to an object rebuilt in this run;
  * every external OAI.* import must be a module tracked at the pinned source
    commit of the original development (a stale object of a deleted module in
    the external cache would otherwise load silently);
  * ComparatorChallenges.* targets are compiled first, into their own root,
    against Mathlib and its dependencies only (no OAI or WeightedQRH roots);
  * independent modules compile concurrently (topological scheduling).
The original QRH and mathlib object caches remain explicit external inputs.
"""
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
from datetime import datetime, timezone
from pathlib import Path
import argparse, json, os, subprocess, sys, time

from verify import CONFIG, ROOT, digest, imports, source, dependency_order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--source-checkout", type=Path,
                        default=ROOT.parents[1] / "formalize_11_12" / "math")
    args = parser.parse_args()
    order, external = dependency_order(args.modules)
    order.sort(key=lambda m: not m.startswith("ComparatorChallenges."))
    git = ["git", "-C", str(args.source_checkout)]
    commit = subprocess.run(git + ["rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    dirty = subprocess.run(git + ["status", "--porcelain"], capture_output=True, text=True, check=True).stdout
    if dirty:
        raise SystemExit("Original-development checkout has uncommitted changes")
    tracked = set(subprocess.run(git + ["ls-files", "lean/OAI"], capture_output=True, text=True,
                                 check=True).stdout.split())
    untracked = [e for e in external if e.startswith("OAI.")
                 and "lean/" + e.replace(".", "/") + ".lean" not in tracked]
    if untracked:
        raise SystemExit(f"External imports absent from source commit {commit}: {untracked}")
    deps = {m: [d for d in imports(source(m)) if d.startswith("WeightedQRH.")] for m in order}
    before = {m: digest(source(m)) for m in order}
    out = args.output_root.resolve()
    for r in (out, out.parent / "challenges"):
        if r.exists() and any(r.rglob("*.olean")):
            raise SystemExit(f"Output root {r} already holds objects; use a fresh directory")
    live = str(ROOT)
    path = [p for p in CONFIG["LEAN_PATH"].split(os.pathsep) if Path(p).resolve() != ROOT]
    assert live not in path
    upstream = ROOT.parents[1] / "formalize_11_12" / "upstream"
    mathlib_only = [p for p in path if not Path(p).resolve().is_relative_to(upstream.resolve())]
    challenges = out.parent / "challenges"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(challenges), str(out)] + path)
    challenge_env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(challenges)] + mathlib_only)}
    logdir = out.parent / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    records = {}
    report = {"started_utc": datetime.now(timezone.utc).isoformat(), "targets": args.modules,
              "lean": CONFIG["lean"], "LEAN_PATH": env["LEAN_PATH"], "output_root": str(out),
              "live_dev_dir_excluded": live, "local_modules": len(order),
              "source_checkout": str(args.source_checkout), "source_commit": commit,
              "challenge_root": str(challenges), "challenge_LEAN_PATH": challenge_env["LEAN_PATH"],
              "flags": ["-DautoImplicit=false", "-M", "8192", "-j", "2", "-R", str(ROOT)],
              "external_imports": external, "modules": records, "status": "running"}

    def save():
        args.report.write_text(json.dumps(report, indent=2) + "\n")

    def build(m):
        challenge = m.startswith("ComparatorChallenges.")
        obj = ((challenges if challenge else out) / m.replace(".", "/")).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = logdir / (m + ".log")
        t = time.time()
        with log.open("w") as f:
            r = subprocess.run([CONFIG["lean"], "-DautoImplicit=false", "-M", "8192", "-j", "2",
                                "-R", str(ROOT), "-o", str(obj), str(source(m))],
                               cwd=ROOT, env=challenge_env if challenge else env,
                               stdout=f, stderr=subprocess.STDOUT)
        return m, r.returncode, time.time() - t, log

    save()
    done, failed, running = set(), [], {}
    with ThreadPoolExecutor(args.jobs) as pool:
        while len(done) < len(order) and not failed:
            first = [m for m in order if m.startswith("ComparatorChallenges.")]
            for m in order:
                if any(c not in done for c in first) and m not in first:
                    continue
                if m not in done and m not in running and all(d in done for d in deps[m]):
                    if len(running) < args.jobs:
                        running[m] = pool.submit(build, m)
            fin, _ = wait(list(running.values()), return_when=FIRST_COMPLETED)
            for fut in fin:
                m, rc, secs, log = fut.result()
                del running[m]
                records[m] = {"source_sha256": before[m], "exit_code": rc, "seconds": round(secs),
                              "log": str(log), "log_sha256": digest(log)}
                print(f"[{len(records)}/{len(order)}] rc={rc} {secs:5.0f}s {m}", flush=True)
                if rc:
                    failed.append(m)
                    print(log.read_text(), file=sys.stderr)
                else:
                    done.add(m)
            save()
        wait(list(running.values()))
    changed = [m for m in order if digest(source(m)) != before[m]]
    report.update(status="failed" if failed else "source_changed" if changed else "compiled",
                  failed=failed, changed_modules=changed,
                  finished_utc=datetime.now(timezone.utc).isoformat())
    save()
    if failed or changed:
        raise SystemExit(f"FAIL failed={failed} changed={changed}")
    print(f"PASS: {len(order)} local modules rebuilt in isolation")


if __name__ == "__main__":
    main()
