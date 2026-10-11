#!/usr/bin/env python3
"""Recompile local source components against explicitly supplied pinned libraries.

This does not replay imported dependencies, canonical targets, or three kernels.
The working directory must be new or empty; no old local .olean is reused.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

MODULES = ["FiniteDeletionBins", "UnmarkedDensity", "BufferedSlot",
           "RestrictedIncumbent", "SixthRowMask", "RawSixthDensity",
           "UniformDensity", "UnmarkedBatch", "ActualUnmarkedInputs", "HeightUniformDensity", "PlainUnmarkedAdapter",
           "SignedRows", "LowSourceAdapters", "RestrictedCanonicalSource",
           "ScaleShortening", "SourceAudit"]
COMPILER_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--library", type=Path, action="append", required=True)
    ap.add_argument("--work-dir", type=Path, required=True)
    args = ap.parse_args()
    lean = args.lean.resolve()
    if sha(lean) != COMPILER_SHA256:
        ap.error("Compiler does not match the pinned Lean 4.34.1 executable")
    libraries = [p.resolve() for p in args.library]
    if any(not p.is_dir() for p in libraries):
        ap.error("Every supplied library must be an existing directory")
    work = args.work_dir.resolve()
    if work.exists() and any(work.iterdir()):
        ap.error("work-dir must be new or empty")
    source = Path(__file__).resolve().parent / "formalization" / "LocalMoment"
    (work / "LocalMoment").mkdir(parents=True, exist_ok=True)
    for name in MODULES:
        shutil.copy2(source / f"{name}.lean", work / "LocalMoment" / f"{name}.lean")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), *map(str, libraries)]))
    report = {
        "schema": "local-moment-component-replay-v1",
        "scope": "Fresh local component compilation against supplied cached dependencies",
        "compiler_sha256": sha(lean),
        "compiler_version": subprocess.check_output([str(lean), "--version"], text=True).strip(),
        "dependency_libraries": list(map(str, libraries)),
        "dependencies_rebuilt": False,
        "full_physical_moment_verified": False,
        "canonical_all_family_targets_verified": False,
        "comparator_verified": False,
        "three_kernels_verified": False,
        "modules": [],
    }
    success = True
    for name in MODULES:
        rel = f"LocalMoment/{name}"
        result = subprocess.run([str(lean), "-o", rel + ".olean", rel + ".lean"],
                                cwd=work, env=env, capture_output=True, text=True)
        log = work / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        item = {"module": "LocalMoment." + name, "source_sha256": sha(source / f"{name}.lean"),
                "exit_code": result.returncode, "log_sha256": sha(log)}
        if result.returncode == 0:
            item["object_sha256"] = sha(work / (rel + ".olean"))
        report["modules"].append(item)
        print(name, "PASS" if result.returncode == 0 else "FAIL", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr)
            success = False
            break
    if success:
        audit = (work / "SourceAudit.log").read_text()
        declarations = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
        expected = re.findall(r"^#print axioms (\S+)", (source / "SourceAudit.lean").read_text(), re.M)
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        report["axioms"] = {n: [a.strip() for a in ax.split(",") if a.strip()]
                            for n, ax in declarations}
        success = set(report["axioms"]) == set(expected) and all(
            set(ax) <= allowed for ax in report["axioms"].values())
    report["component_checks_passed"] = success
    (work / "component-replay.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
