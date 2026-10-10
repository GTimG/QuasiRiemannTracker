"""Rebuild a target and every local Lean dependency in topological order.

The original QRH and mathlib object cache is an explicit external dependency.
Successful compilation checks proofs, not whether a theorem's assumptions meet
the research objective. In particular, a conditional endpoint stays conditional.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
CONFIG = json.loads((ROOT / "lean_environment.json").read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(module):
    return (ROOT / module.replace(".", "/")).with_suffix(".lean")


def imports(path):
    # The local tree uses ordinary one-line imports. Comments are excluded.
    text = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
    return [name for line in text.splitlines()
            if line.strip().startswith("import ")
            for name in line.split("--", 1)[0].split()[1:]]


def dependency_order(targets):
    order, active, done, external = [], set(), set(), set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError(f"Cyclic local import: {module}")
        path = source(module)
        if not path.exists():
            raise FileNotFoundError(path)
        active.add(module)
        for dep in imports(path):
            if dep.startswith("WeightedQRH."):
                visit(dep)
            else:
                external.add(dep)
        active.remove(module)
        done.add(module)
        order.append(module)

    for target in targets:
        visit(target)
    return order, sorted(external)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--report", type=Path, default=ROOT / "verification_run.json")
    parser.add_argument("--output-root", type=Path,
                        default=ROOT / ".verification" / "lib" / "lean")
    args = parser.parse_args()
    order, external = dependency_order(args.modules)
    if args.plan:
        print(json.dumps({"targets": args.modules, "local_modules": len(order),
                          "external_imports": len(external), "order": order}, indent=2))
        return
    before = {m: digest(source(m)) for m in order}
    env = os.environ.copy()
    args.output_root = args.output_root.resolve()
    # Keep the live development objects untouched. Every local dependency is
    # rebuilt here before a dependent module can resolve it.
    env["LEAN_PATH"] = str(args.output_root) + os.pathsep + CONFIG["LEAN_PATH"]
    records = []
    report = {"started_utc": datetime.now(timezone.utc).isoformat(),
              "targets": args.modules, "environment": CONFIG,
              "output_root": str(args.output_root),
              "external_imports": external, "modules": records,
              "status": "running",
              "scope": "Compilation against supplied external object caches; inspect theorem assumptions separately."}

    def save():
        args.report.write_text(json.dumps(report, indent=2) + "\n")

    save()
    for index, module in enumerate(order, 1):
        # Refuse a moving source tree instead of certifying a mixed snapshot.
        changed = [m for m in order if digest(source(m)) != before[m]]
        if changed:
            report.update(status="source_changed", changed_modules=changed)
            save()
            raise SystemExit("Source changed during verification: " + ", ".join(changed))
        path = source(module)
        object_path = (args.output_root / module.replace(".", "/")).with_suffix(".olean")
        object_path.parent.mkdir(parents=True, exist_ok=True)
        log = ROOT / "logs" / (module + ".verify.log")
        print(f"[{index}/{len(order)}] {module}", flush=True)
        with log.open("w") as output:
            result = subprocess.run(
                [CONFIG["lean"], "-DautoImplicit=false", "-M", "8192", "-j", "2",
                 "-R", str(ROOT), "-o", str(object_path), str(path)],
                cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
        records.append({"module": module, "source_sha256": before[module],
                        "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                        "exit_code": result.returncode})
        save()
        if result.returncode:
            report["status"] = "failed"
            save()
            print(log.read_text(), file=sys.stderr)
            raise SystemExit(result.returncode)
    changed = [m for m in order if digest(source(m)) != before[m]]
    report.update(status="source_changed" if changed else "compiled",
                  changed_modules=changed,
                  finished_utc=datetime.now(timezone.utc).isoformat())
    save()
    if changed:
        raise SystemExit("Source changed during verification")
    print(f"PASS: {len(order)} local modules rebuilt; theorem scope remains a separate audit.")


if __name__ == "__main__":
    main()
