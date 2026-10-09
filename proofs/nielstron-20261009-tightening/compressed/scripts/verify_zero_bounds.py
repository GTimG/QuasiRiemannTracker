#!/usr/bin/env python3
"""Check the original targets and the equivalent, readable zero bounds."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

R = Path(__file__).resolve().parents[1]


def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


# Recheck the whole dependency graph, original specifications and axioms before
# relying on the compiled nonvanishing theorems in the presentation module.
with (R / "logs/local-verification-run.log").open("w") as log:
    subprocess.run([sys.executable, str(R / "scripts/verify_cached.py")],
                   check=True, stdout=log, stderr=subprocess.STDOUT)
original = json.loads((R / "audit/local-verification.json").read_text())
assert original["status"] == "PASS"

gate = R / "audit/ZeroBoundsEquivalence.lean"
lean = R / "toolchains/lean-4.34.1-linux/bin/lean"
threads = min(16, len(os.sched_getaffinity(0))) if hasattr(os, "sched_getaffinity") else min(16, os.cpu_count() or 1)
env = os.environ.copy()
env["LEAN_PATH"] = (R / "audit/local-lean-path.txt").read_text().strip()
env["GLIBC_TUNABLES"] = "glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1"
log = R / "logs/local-zero-bounds-equivalence.log"
with log.open("w") as f:
    subprocess.run([str(lean), f"-j{threads}", "-DautoImplicit=false", str(gate)],
                   env=env, check=True, stdout=f, stderr=subprocess.STDOUT)

output = log.read_text()
groups = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
groups += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
expected = {
    "QRH.riemannZeta_zero_re_le",
    "QRH.DirichletCharacter.zero_re_le_or_exception",
    "QRH.Hecke.zero_re_le_or_exception",
    "QRH.DirichletCharacter.zero_re_le",
    "QRH.Hecke.zero_re_le",
    "QRH.ZeroBoundsEquivalence.zeta",
    "QRH.ZeroBoundsEquivalence.dirichlet",
    "QRH.ZeroBoundsEquivalence.hecke",
}
assert len(groups) == len(expected) and {name for name, _ in groups} == expected, output
axioms = {name: sorted(a.strip() for a in values.split(",") if a.strip())
          for name, values in groups}
assert all(set(values) <= {"propext", "Classical.choice", "Quot.sound"}
           for values in axioms.values()), axioms

report = {
    "status": "PASS",
    "original_exact_three_targets_proved": original["exact_three_targets_proved"],
    "three_zero_classifications_proved_equivalent_to_independent_targets": True,
    "public_results": 5,
    "declarations": axioms,
    "compiler": original["compiler"],
    "thread_budget": threads,
    "artifacts": {str(p.relative_to(R)): {"sha256": sha(p)} for p in (
        gate, log, R / "formalization/QRH/ZeroBounds.lean",
        R / "build/local/QRH/ZeroBounds.olean", R / "audit/local-verification.json",
    )},
}
(R / "audit/zero-bounds-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
