#!/usr/bin/env python3
"""Check independent literal tighter targets while preserving all old targets."""
from pathlib import Path
from fractions import Fraction
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

R = Path(__file__).resolve().parents[1]
OLD = Fraction(874957019421, 1000000000000)


def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerator", type=int, required=True)
    parser.add_argument("--denominator", type=int, required=True)
    args = parser.parse_args()
    if args.denominator <= 0:
        parser.error("The denominator must be positive")
    bound = Fraction(args.numerator, args.denominator)
    if not 0 < bound < OLD:
        parser.error("The proposed bound must strictly improve the original")
    assert sha(R / "formalization/QRH/Nonvanishing.lean") == \
        "22f3bc70ad34306037602b633e2d024a7fc86da419bcc1d1bd9b443c21fc471f", \
        "Protected original final theorem source changed"
    preparation = json.loads((R / "audit/tightening-preparation.json").read_text())
    for name, record in preparation["protected_files"].items():
        assert sha(R / "formalization" / name) == record["sha256"], name

    # This first runs all original statement, provenance, source and axiom checks.
    with (R / "logs/local-zero-bounds-verification-run.log").open("w") as log:
        subprocess.run([sys.executable, str(R / "scripts/verify_zero_bounds.py")],
                       check=True, stdout=log, stderr=subprocess.STDOUT)
    old_verification = json.loads((R / "audit/local-verification.json").read_text())
    assert old_verification["status"] == "PASS"

    literal = f"({bound.numerator} / {bound.denominator} : ℝ)"
    specification = R / "audit/TightIndependentTargets.lean"
    specification.write_text(f'''import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

/-! Literal targets, compiled without importing QRH or its geometry. -/
namespace QRH.TightIndependent
open scoped _root_.DirichletCharacter

def allDirichlet : Prop :=
  ∀ {{q : ℕ}} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {{s : ℂ}},
    {literal} < s.re → ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0

def zeta : Prop := ∀ {{s : ℂ}},
  {literal} < s.re → _root_.riemannZeta s ≠ 0

def allHecke : Prop :=
  ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    {literal} < s.re → (s ≠ 1 ∨ χ.residue ≠ 1) →
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0
end QRH.TightIndependent
''')
    gate = R / "audit/TightTargetsRequired.lean"
    gate.write_text(f'''import TightIndependentTargets
import QRH

example : QRH.TightIndependent.allDirichlet :=
  @QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
example : QRH.TightIndependent.zeta :=
  @QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
example : QRH.TightIndependent.allHecke :=
  @QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re
example : QRH.theta = (874957019421 / 1000000000000 : ℝ) := rfl
example : QRH.tightTheta = {literal} := rfl
example : {literal} < (874957019421 / 1000000000000 : ℝ) :=
  QRH.tightTheta_lt_theta

#print axioms QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
#print axioms QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_zero_re_le_tightTheta
#print axioms QRH.tightTheta_lt_theta
''')
    lean = R / "toolchains/lean-4.34.1-linux/bin/lean"
    out = R / "build/tight-gate"
    out.mkdir(parents=True, exist_ok=True)
    threads = min(16, len(os.sched_getaffinity(0))) if hasattr(os, "sched_getaffinity") else min(16, os.cpu_count() or 1)
    env = os.environ.copy()
    env["LEAN_PATH"] = (R / "audit/local-lean-path.txt").read_text().strip()
    env["GLIBC_TUNABLES"] = "glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1"
    log = R / "logs/local-tight-targets-required.log"
    with log.open("w") as f:
        subprocess.run([str(lean), f"-j{threads}", "-DautoImplicit=false", "-o",
                        str(out / "TightIndependentTargets.olean"), specification.name],
                       cwd=R / "audit", env=env, check=True, stdout=f, stderr=subprocess.STDOUT)
        env["LEAN_PATH"] = str(out) + os.pathsep + env["LEAN_PATH"]
        subprocess.run([str(lean), f"-j{threads}", "-DautoImplicit=false", gate.name],
                       cwd=R / "audit", env=env, check=True, stdout=f, stderr=subprocess.STDOUT)
    output = log.read_text()
    groups = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    groups += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    expected = {
        "QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re",
        "QRH.riemannZeta_ne_zero_of_tightTheta_lt_re",
        "QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re",
        "QRH.riemannZeta_zero_re_le_tightTheta", "QRH.tightTheta_lt_theta",
    }
    assert len(groups) == len(expected) and {name for name, _ in groups} == expected, output
    axioms = {name: sorted(a.strip() for a in values.split(",") if a.strip())
              for name, values in groups}
    assert all(set(values) <= {"propext", "Classical.choice", "Quot.sound"}
               for values in axioms.values()), axioms
    report = {
        "status": "PASS", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "original_exact_three_targets_proved": True,
        "original_protected_sources_unchanged": sorted(preparation["protected_files"]),
        "tighter_exact_three_targets_proved": True,
        "original_threshold": str(OLD), "threshold": str(bound),
        "exact_improvement": str(OLD - bound), "strict_improvement_proved_in_lean": True,
        "specification_compiled_without_QRH_imports": True,
        "declarations": axioms, "compiler": old_verification["compiler"],
        "thread_budget": threads,
        "artifacts": {str(p.relative_to(R)): {"sha256": sha(p)} for p in (
            specification, gate, log, out / "TightIndependentTargets.olean",
            R / "audit/local-verification.json", R / "audit/zero-bounds-verification.json",
            R / "formalization/QRH/TighterNonvanishing.lean",
        )},
        "external_checker_status": "Not checked by Comparator, NanoDa or con-ron in this local Lean gate.",
    }
    (R / "audit/tightening-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
