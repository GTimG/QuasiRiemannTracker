"""Three-kernel judge of the theta = 10499/12000 statements (Lean, NanoDa, con-ron).

Follows the protocol of the tracker's earlier kernel dossiers (PalomarSubmission
d4e41c1 driving `lake comparator` from Lean v4.35.0-rc2), adapted to run here:

  * preflight controls on the judge toolchain before any proof is judged: a matching
    pair must pass, a mismatched statement must be rejected by Comparator, and an
    ill-typed proof (theorem value replaced by its type in the export) must be
    rejected by the kernels, including Lean's own;
  * the Challenge is the tracker's fixed three-target template with only the rational
    literal replaced, compiled with Lean 4.34.1 against PRISTINE openai/math fd4aeeb2e
    (Hecke/IdealBridge closure) and Mathlib d13f23b7, so that Comparator checks the
    proof's definitions against upstream ones;
  * the Solution wrapper imports the proof and restates the three theorems;
  * both are exported with lean4export 076e8e5 and judged by
    `lake comparator --challenge-from-export --solution-from-export` with nanoda_bin
    and con-ron (--jobs=2) as external kernels after Lean's default kernel.

Differences from the precedent, recorded in result.json: macOS arm64 binaries from the
official v4.35.0-rc2 darwin_aarch64 release instead of linux x86_64, and no bubblewrap
sandbox (`--inadvisably-no-sandbox`; Comparator's sandbox needs Linux namespaces).
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse, hashlib, json, os, platform, re, shutil, subprocess, sys, time

TEMPLATE_LITERAL = "874957019421 / 1000000000000"
THETA = ("10499", "12000")
THEOREMS = ["QRHPalomar.allDirichlet", "QRHPalomar.zeta", "QRHPalomar.allHecke"]
AXIOMS = ["Classical.choice", "Quot.sound", "propext"]
SOLUTION = """import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import WeightedQRH.Statements

namespace QRHPalomar
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re χ hs hpole

theorem zeta {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact OAI.riemannZeta_ne_zero_of_10499_12000_lt_re hs

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact WeightedQRH.hecke_nonzero χ s hs hpole
end QRHPalomar
"""
PREFLIGHT = {
    "PreflightChallenge": "theorem palomar_preflight : True := trivial\n",
    "PreflightSolution": "theorem palomar_preflight : True := trivial\n",
    "PreflightWrong": "theorem palomar_preflight : True ∧ True := ⟨trivial, trivial⟩\n",
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def lake_lean_path(workspace, lake434):
    out = subprocess.run([str(lake434), "env", "printenv", "LEAN_PATH"], cwd=workspace,
                         capture_output=True, text=True, check=True)
    return out.stdout.strip()


def run(cmd, log, env, cwd, stdout_path=None):
    t = time.time()
    with open(log, "w") as lf:
        if stdout_path is None:
            p = subprocess.run(cmd, cwd=cwd, env=env, stdout=lf, stderr=subprocess.STDOUT)
        else:
            with open(stdout_path, "wb") as of:
                p = subprocess.run(cmd, cwd=cwd, env=env, stdout=of, stderr=lf)
    return p.returncode, round(time.time() - t, 1)


def primitive_targets(judge_prefix):
    text = (judge_prefix / "src/lean/lake/Lake/CLI/Check.lean").read_text()
    body = re.search(r"^def primitiveTargets[^\n]*\n(?P<b>.*?)^def ", text, re.M | re.S).group("b")
    body = re.sub(r"/-.*?-/", "", body, flags=re.S)
    body = "\n".join(line.split("--", 1)[0] for line in body.splitlines())
    items = re.fullmatch(r"\s*return\s*#\[(?P<i>[^\[\]]*)\]\s*", body).group("i")
    return [re.fullmatch(r"``([A-Za-z_][A-Za-z0-9_'.]*)", x.strip()).group(1)
            for x in items.split(",") if x.strip()]


def ill_typed_export(source, theorem, dest):
    records = [json.loads(line) for line in source.read_bytes().split(b"\n") if line.strip()]
    name = next(r["in"] for r in records if "in" in r and r.get("str", {}).get("str") == theorem)
    for i, r in enumerate(records):
        d = r.get("thm")
        if isinstance(d, dict) and d.get("name") == name:
            d["value"] = d["type"]
            records[i] = {"thm": d}
            break
    else:
        raise SystemExit(f"no theorem record for {theorem}")
    dest.write_bytes(b"".join(json.dumps(r, separators=(",", ":")).encode() + b"\n" for r in records))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--solution-workspace", type=Path, required=True)
    ap.add_argument("--challenge-workspace", type=Path, required=True)
    ap.add_argument("--template", type=Path, required=True,
                    help="tracker public/proofs/palomar-20261009/qrh/src/Challenge.lean")
    ap.add_argument("--source-lean", type=Path, required=True, help="Lean 4.34.1 prefix")
    ap.add_argument("--judge-lean", type=Path, required=True, help="Lean 4.35.0-rc2 prefix")
    ap.add_argument("--lean4export", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--preflight-only", action="store_true")
    a = ap.parse_args()
    out = a.out.resolve()
    if out.exists():
        raise SystemExit(f"{out} exists; use a fresh directory")
    for d in ("src", "lib-challenge", "lib-solution", "exports", "logs", "controls/src",
              "controls/lib", "controls/exports", "judge/home", "judge/tmp", "judge/project"):
        (out / d).mkdir(parents=True)
    lean434, lake434 = a.source_lean / "bin/lean", a.source_lean / "bin/lake"
    J = a.judge_lean.resolve()
    tools = {n: J / "bin" / n for n in ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")}
    kernels = {"nanoda": [str(tools["nanoda_bin"])], "con-ron": [str(tools["con-ron"]), "--jobs=2"]}
    report = {"status": "running", "started_utc": now(), "theta": "/".join(THETA),
              "declarations": THEOREMS, "allowed_axioms": AXIOMS,
              "kernels": ["Lean default", "nanoda", "con-ron"], "phases": [],
              "runner": {"platform": platform.platform(), "machine": platform.machine(),
                         "python": sys.version.split()[0]},
              "sandbox": "none: lake comparator --inadvisably-no-sandbox (bubblewrap needs Linux)",
              "source_compiler": "4.34.1", "judge_toolchain": "4.35.0-rc2",
              "tool_sha256": {**{k: sha256(v) for k, v in tools.items()},
                              "source_lean": sha256(lean434), "lean4export": sha256(a.lean4export)}}
    save = lambda: (out / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    save()
    base_env = {"PATH": f"{J}/bin:/usr/bin:/bin", "LEAN_ABORT_ON_PANIC": "1",
                "HOME": str(out / "judge/home"), "TMPDIR": str(out / "judge/tmp")}
    targets = (["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + THEOREMS + AXIOMS
               + primitive_targets(J))
    (out / "export-targets.json").write_text(json.dumps(targets, indent=2) + "\n")

    def judge(config, challenge, solution, log):
        return run([str(tools["lake"]), "comparator", "--inadvisably-no-sandbox", "--config", str(config),
                    "--challenge-from-export", str(challenge), "--solution-from-export", str(solution)],
                   log, base_env, out / "judge/project")

    # 1. Preflight controls on the judge toolchain, before the proof is judged.
    t0 = now()
    c = out / "controls"
    pf_targets = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "palomar_preflight"] + AXIOMS + primitive_targets(J)
    env = {**base_env, "LEAN_PATH": f"{c / 'lib'}:{J / 'lib/lean'}"}
    for m, text in PREFLIGHT.items():
        (c / "src" / f"{m}.lean").write_text(text)
        rc, _ = run([str(tools["lean"]), "-o", str(c / "lib" / f"{m}.olean"), str(c / "src" / f"{m}.lean")],
                    c / f"{m}-compile.log", env, c)
        assert rc == 0, m
        rc, _ = run([str(tools["leanexport"]), m, "--", *pf_targets], c / f"{m}-export.log", env, c,
                    stdout_path=c / "exports" / f"{m}.export")
        assert rc == 0, m
    ill_typed_export(c / "exports/PreflightSolution.export", "palomar_preflight",
                     c / "exports/PreflightIllTyped.export")
    pf_config = c / "comparator.json"
    pf_config.write_text(json.dumps({"challenge_module": "PreflightChallenge", "solution_module": "PreflightSolution",
                                     "theorem_names": ["palomar_preflight"], "definition_names": [],
                                     "permitted_axioms": AXIOMS, "external_kernels": kernels}, indent=2) + "\n")
    cases = []
    for name, sol, log in [("matching", "PreflightSolution", "matching.log"),
                           ("mismatched", "PreflightWrong", "mismatched.log"),
                           ("ill-typed", "PreflightIllTyped", "ill-typed.log")]:
        rc, secs = judge(pf_config, c / "exports/PreflightChallenge.export", c / "exports" / f"{sol}.export", c / log)
        cases.append({"name": name, "exit_code": rc, "seconds": secs, "log": f"controls/{log}"})
    logs = {x["name"]: (out / x["log"]).read_text() for x in cases}
    ok = (cases[0]["exit_code"] == 0 and "Your solution is okay!" in logs["matching"]
          and all(f"{k} kernel accepts the solution" in logs["matching"] for k in ("con-ron", "nanoda", "Lean default"))
          and cases[1]["exit_code"] == 1 and "statement do not match" in logs["mismatched"]
          and cases[2]["exit_code"] == 1 and "Lean default kernel rejected the solution" in logs["ill-typed"])
    (out / "control-results.json").write_text(json.dumps({"cases": cases}, indent=2) + "\n")
    report["phases"].append({"name": "preflight-controls", "started_utc": t0, "finished_utc": now(), "passed": ok})
    report["preflight"] = "passed" if ok else "FAILED"
    save()
    if not ok:
        report["status"] = "FAIL"; save(); raise SystemExit("preflight controls failed")
    if a.preflight_only:
        print("preflight passed", [(x["name"], x["exit_code"]) for x in cases]); return

    # 2. Challenge (pristine upstream definitions) and Solution sources.
    template = a.template.read_text()
    assert template.count(TEMPLATE_LITERAL) == 3
    (out / "src/Challenge.lean").write_text(template.replace(TEMPLATE_LITERAL, " / ".join(THETA)))
    (out / "src/Solution.lean").write_text(SOLUTION)
    report["challenge_template_sha256"] = sha256(a.template)
    report["challenge_sha256"] = sha256(out / "src/Challenge.lean")
    report["solution_sha256"] = sha256(out / "src/Solution.lean")
    ch_path = lake_lean_path(a.challenge_workspace, lake434)
    so_path = lake_lean_path(a.solution_workspace, lake434)
    assert "WeightedQRH" not in ch_path and str(a.solution_workspace.resolve()) not in ch_path
    report["challenge_LEAN_PATH"], report["solution_LEAN_PATH"] = ch_path, so_path

    t0 = now()
    for mod, lib, path in [("Challenge", "lib-challenge", ch_path), ("Solution", "lib-solution", so_path)]:
        env = {**base_env, "PATH": f"{a.source_lean}/bin:/usr/bin:/bin", "LEAN_PATH": f"{out / lib}:{path}"}
        rc, secs = run([str(lean434), "-R", str(out / "src"), "-o", str(out / lib / f"{mod}.olean"),
                        str(out / "src" / f"{mod}.lean")], out / "logs" / f"{mod}-compile.log", env, out)
        report["phases"].append({"name": f"compile-{mod}", "exit_code": rc, "seconds": secs})
        save()
        if rc:
            report["status"] = "FAIL"; save(); raise SystemExit(f"{mod} failed to compile")
        rc, secs = run([str(a.lean4export), mod, "--", *targets], out / "logs" / f"{mod}-export.log", env, out,
                       stdout_path=out / "exports" / f"{mod}.export")
        head = (out / "exports" / f"{mod}.export").open("rb").readline(4096)
        report["phases"].append({"name": f"export-{mod}", "exit_code": rc, "seconds": secs,
                                 "header_ok": head.startswith(b'{"meta":')})
        save()
        if rc or not head.startswith(b'{"meta":'):
            report["status"] = "FAIL"; save(); raise SystemExit(f"{mod} export failed")
    report["exports"] = {m: {"sha256": sha256(out / "exports" / f"{m}.export"),
                             "bytes": (out / "exports" / f"{m}.export").stat().st_size}
                         for m in ("Challenge", "Solution")}
    report["phases"].append({"name": "compile-and-export", "started_utc": t0, "finished_utc": now()})
    save()

    # 3. Judge: Comparator statement/definition/axiom check, then con-ron, nanoda, Lean's kernel.
    config = out / "comparator.json"
    config.write_text(json.dumps({"challenge_module": "Challenge", "solution_module": "Solution",
                                  "theorem_names": THEOREMS, "definition_names": [],
                                  "permitted_axioms": AXIOMS, "external_kernels": kernels}, indent=2) + "\n")
    t0 = now()
    rc, secs = judge(config, out / "exports/Challenge.export", out / "exports/Solution.export", out / "judge.log")
    log = (out / "judge.log").read_text()
    markers = {k: f"{k} kernel accepts the solution" in log for k in ("con-ron", "nanoda", "Lean default")}
    passed = rc == 0 and all(markers.values()) and "Your solution is okay!" in log
    report["phases"].append({"name": "judge", "started_utc": t0, "finished_utc": now(), "exit_code": rc,
                             "seconds": secs})
    report["acceptance_markers"] = markers
    report["judge_exit_code"] = rc
    report["status"] = "PASS" if passed else "FAIL"
    report["verified_at_utc"] = now() if passed else ""
    report["artifacts"] = {str(p.relative_to(out)): sha256(p) for p in sorted(out.rglob("*"))
                           if p.is_file() and p.suffix not in (".export", ".olean", ".ilean")
                           and p.name != "result.json" and "judge/" not in str(p.relative_to(out))}
    save()
    print(report["status"], markers, rc)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
