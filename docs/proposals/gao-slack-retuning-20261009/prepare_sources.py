#!/usr/bin/env python3
"""Prepare an uncompiled QRH slack-retuning source overlay. Never runs Lean."""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

PACKET = Path(__file__).resolve().parent
PROJECT = PACKET.parents[2]
BUILD = PROJECT / "build/gao-slack-retuning-20261009"
PIN = "40844a7614b67840801e65b836b3da2e1f7ff029"
SOURCE_PREFIX = "proofs/nielstron-20261009-tightening/compressed/formalization"
OLD = Q(874957019420098946128604623, 10**27)
NEW = Q(437478509710049473064301925667, 5*10**29)
MARGIN, OLD_MARGIN = Q(5, 10**27), Q(5, 10**24)
ZETA, T_CAP = Q(1, 10**29), Q(1, 10**31)
PROTECTED = (
    "QRH/DirichletTargets.lean", "QRH/HeckeTargets.lean",
    "QRH/IndependentTargets.lean", "QRH/Nonvanishing.lean",
    "QRH/StatementParity.lean", "QRH/ZeroBounds.lean", "QRH/ZetaTransfer.lean",
)
# Counts are audited against the pinned working source, not inferred after mutation.
BUDGETS = {
    "OptimizedAdaptiveSaving.lean": {24: 1},
    "ActualCubeArithmeticSaving.lean": {24: 1},
    "ActualNormalizedNonfloorCube.lean": {24: 1},
    "OptimizedMixedSaving.lean": {24: 2},
    "OptimizedData.lean": {24: 1, 28: 3},
    "ActualNonfloorCubeNorm.lean": {24: 1},
    "OptimizedTransportBudget.lean": {28: 1},
    "CompleteNonfloorCubeData.lean": {28: 1},
    "CompleteNonfloorRowsData.lean": {28: 1},
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(data) -> bytes:
    return (json.dumps(data, indent=2, sort_keys=True) + "\n").encode()


def inventory(directory: Path) -> dict[str, str]:
    return {p.relative_to(directory).as_posix(): sha(p.read_bytes())
            for p in sorted(directory.rglob("*")) if p.is_file()}


def replace_token(text: str, old: str, new: str, expected: int) -> str:
    out, count = re.subn(r"(?<![0-9])" + re.escape(old) + r"(?![0-9])", new, text)
    if count != expected:
        raise ValueError(f"Expected {expected} replacements of {old}; found {count}")
    return out


def wrapper_source() -> str:
    value = f"({NEW.numerator} / {NEW.denominator} : ℝ)"
    old = f"({OLD.numerator} / {OLD.denominator} : ℝ)"
    return f'''import QRH.TighterNonvanishing

/-! UNCOMPILED source overlay. Literal stronger targets, with original definitions
and pole exceptions. No new analytic result is asserted by source preparation. -/
namespace QRH
open scoped _root_.DirichletCharacter

 theorem Hecke.LFunction_ne_zero_of_slackRefined_lt_re
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : {value} < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 :=
  Hecke.LFunction_ne_zero_of_tightTheta_lt_re χ s
    (by simpa only [tightTheta] using hs) hpole

 theorem DirichletCharacter.LFunction_ne_zero_of_slackRefined_lt_re
    {{q : ℕ}} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {{s : ℂ}}
    (hs : {value} < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re χ
    (by simpa only [tightTheta] using hs) hexc

 theorem riemannZeta_ne_zero_of_slackRefined_lt_re {{s : ℂ}}
    (hs : {value} < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_tightTheta_lt_re
    (by simpa only [tightTheta] using hs)

 theorem riemannZeta_zero_re_le_slackRefined {{s : ℂ}}
    (hz : riemannZeta s = 0) : s.re ≤ {value} :=
  le_of_not_gt fun hs => riemannZeta_ne_zero_of_slackRefined_lt_re hs hz

 theorem slackRefined_lt_tracker : {value} < {old} := by
  norm_num

end QRH
'''.replace("\n theorem", "\ntheorem")


def prepare(source: Path, output: Path, report: Path, patch: Path) -> dict:
    if output == source or source in output.parents:
        raise ValueError("Output must not mutate the input source tree")
    present = inventory(source)
    expected = json.loads((PACKET / "inputs/source_manifest.json").read_text())
    # The public baseline also carries a non-mathematical token-count helper.
    # It is not copied into the candidate or used by this preparation program.
    extra = set(present) - set(expected)
    if extra - {"proof_length.py"}:
        raise ValueError(f"Unexpected baseline assets: {sorted(extra)}")
    actual_inventory = {name: present.get(name) for name in expected}
    if actual_inventory != expected:
        raise ValueError("Input source bytes differ from the pinned manifest")
    originals = {name: (source / name).read_bytes() for name in actual_inventory}
    transformed = dict(originals)
    changes = []
    scripts = PACKET / "inputs/scripts"
    expected_scripts = json.loads((PACKET / "inputs/script_manifest.json").read_text())
    actual_scripts = {name: sha((scripts / name).read_bytes()) for name in expected_scripts}
    if actual_scripts != expected_scripts:
        raise ValueError("Pinned coefficient generator/model bytes changed")
    sys.path.insert(0, str(scripts))
    import certificate_model as model
    import update_certificate as generator
    cert = model.certificate(NEW)
    checks = model.validate(cert, margin=MARGIN, zeta=ZETA, t_cap=T_CAP)
    if len(checks) != 22 or not all(checks.values()):
        raise ValueError(f"Actual-budget arithmetic checks failed: {checks}")
    cert_path = "QRH/Certificate.lean"
    new_cert, coefficient_metadata = generator.update(
        originals[cert_path].decode(), NEW, parameter_name="tightTheta",
        margin=MARGIN, old_theta=OLD, source_parameter_name="tightTheta",
        old_margin=OLD_MARGIN)
    coefficient_metadata["improvement_vs_source_theta"] = str(OLD-NEW)
    coefficient_metadata["original_theta_comparison_is_proofcouncil_not_latest_tracker"] = True
    transformed[cert_path] = new_cert.encode()
    geometry_path = "QRH/Geometry.lean"
    geometry = originals[geometry_path].decode()
    old_def = f"def tightTheta : ℝ := ({OLD.numerator} / {OLD.denominator} : ℝ)"
    new_def = f"def tightTheta : ℝ := ({NEW.numerator} / {NEW.denominator} : ℝ)"
    if geometry.count(old_def) != 1:
        raise ValueError("Working threshold definition differs from pinned input")
    geometry = geometry.replace(old_def, new_def)
    geometry = replace_token(geometry, str(10**26), str(10**29), 1)
    transformed[geometry_path] = geometry.encode()
    for short, powers in BUDGETS.items():
        name = "QRH/Detector/" + short
        source_text = originals[name].decode()
        for old_power, count in powers.items():
            source_text = replace_token(source_text, str(10**old_power),
                                        str(10**(old_power+3)), count)
        transformed[name] = source_text.encode()
    # Frozen original final targets and the existing stronger wrapper remain byte-identical.
    for name in PROTECTED + ("QRH/TighterNonvanishing.lean",):
        if transformed[name] != originals[name]:
            raise ValueError("Frozen final source changed: " + name)
    original_definition = "def theta : ℝ := (874957019421 / 1000000000000 : ℝ)"
    if originals[geometry_path].decode().count(original_definition) != 1 or \
       transformed[geometry_path].decode().count(original_definition) != 1:
        raise ValueError("Original QRH.theta definition was not preserved")
    new_wrapper_path = "QRH/SlackRefinedNonvanishing.lean"
    if new_wrapper_path in transformed:
        raise ValueError("New literal target path already exists")
    transformed[new_wrapper_path] = wrapper_source().encode()
    transformed["QRH.lean"] = b"import QRH.SlackRefinedNonvanishing\n" + originals["QRH.lean"]
    output.mkdir(parents=True, exist_ok=True)
    unexpected = set(inventory(output)) - transformed.keys()
    if unexpected:
        raise ValueError(f"Unexpected existing output files: {sorted(unexpected)}")
    all_patch = []
    for name in sorted(transformed):
        before, after = originals.get(name, b""), transformed[name]
        dest = output / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(after)
        if before != after:
            changes.append({"path": name, "before_sha256": sha(before) if name in originals else None,
                            "after_sha256": sha(after), "kind": "modified" if name in originals else "added"})
            all_patch.extend(difflib.unified_diff(
                before.decode().splitlines(keepends=True), after.decode().splitlines(keepends=True),
                fromfile="a/formalization/"+name if name in originals else "/dev/null",
                tofile="b/formalization/"+name))
    patch.parent.mkdir(parents=True, exist_ok=True)
    report.parent.mkdir(parents=True, exist_ok=True)
    patch.write_text("".join(all_patch))
    after_inventory = inventory(output)
    protected_hashes = {name: {"sha256": sha(originals[name]), "unchanged": True} for name in PROTECTED}
    exact_record = {key: str(value) for key, value in cert.items() if isinstance(value, Q)}
    # This is a static source dependency inventory, not a compiler/kernel result.
    module_paths = {
        "QRH" if name == "QRH.lean" else name[:-5].replace("/", "."): name
        for name in transformed
        if name == "QRH.lean" or (name.startswith("QRH/") and name.endswith(".lean"))
    }
    import_graph = {}
    external_imports = set()
    for module, name in sorted(module_paths.items()):
        imports = []
        for match in re.finditer(r"(?m)^import\s+([^\n]+)$", transformed[name].decode()):
            imports.extend(match.group(1).split())
        local = [item for item in imports if item in module_paths]
        missing = [item for item in imports if item.startswith("QRH.") and item not in module_paths]
        if missing:
            raise ValueError(f"Missing local QRH import(s) in {module}: {missing}")
        external_imports.update(item for item in imports if item not in module_paths)
        import_graph[module] = local
    seen, visiting = set(), set()
    def visit(module):
        if module in visiting:
            raise ValueError("QRH import cycle: " + module)
        if module in seen:
            return
        visiting.add(module)
        for dep in import_graph[module]:
            visit(dep)
        visiting.remove(module)
        seen.add(module)
    for module in import_graph:
        visit(module)
    changed_paths = {item["path"] for item in changes}
    affected = {module for module, name in module_paths.items() if name in changed_paths}
    while True:
        grown = affected | {module for module, deps in import_graph.items() if any(dep in affected for dep in deps)}
        if grown == affected:
            break
        affected = grown
    rebuild = {
        "status": "STATIC_DEPENDENCY_INVENTORY_NOT_COMPILED",
        "all_local_sources_reinstantiated_under_new_geometry": True,
        "all_qrh_modules_require_source_cohort_review_and_rebuild": sorted(module_paths),
        "geometry_budget_reverse_import_closure": sorted(affected),
        "direct_external_imports": sorted(external_imports),
        "local_import_graph": import_graph,
        "acyclic_local_import_graph": True,
        "full_transitive_external_closure": "NOT_REBUILT_OR_ENUMERATED",
        "note": "Unchanged source bytes can change meaning through QRH.Geometry.tightTheta; original compiled APIs must not be reused as proofs for this cohort.",
    }
    (report.parent / "dependency_rebuild_inventory.json").write_bytes(canonical(rebuild))
    result = {
        "status": "UNCOMPILED_SOURCE_RETUNING_ONLY",
        "script": "prepare_sources.py",
        "script_sha256": sha(Path(__file__).read_bytes()),
        "analytic_certificate": False, "new_record_claim": False,
        "lean_executed": False, "kernel_check_executed": False,
        "tracker_pin": PIN, "source_prefix": SOURCE_PREFIX,
        "openai_analytic_pin": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "candidate": str(NEW), "benchmark": str(OLD), "strict_improvement": str(OLD-NEW),
        "budgets": {"F_margin": str(MARGIN), "E_margin": str(Q(2, 5)*MARGIN),
                    "central_loss": str(Q(1, 10**27)), "zeta": str(ZETA), "t_cap": str(T_CAP)},
        "actual_budget_checks": checks,
        "checks_are_arithmetic_not_analytic": True,
        "complete_loss_coefficient": str(Q(18)+Q(185, 2000)),
        "complete_loss_upper_budget_ratio": str((19*T_CAP+2*ZETA)/Q(1, 10**27)),
        "exact_geometry": exact_record,
        "coefficient_metadata": coefficient_metadata,
        "original_theta_definition_preserved": original_definition,
        "frozen_original_final_sources": protected_hashes,
        "existing_tighter_wrapper_source_unchanged": True,
        "existing_tighter_wrapper_semantics_unchanged": False,
        "working_tightTheta_intentionally_changed": True,
        "dependency_rebuild_inventory_sha256": sha(canonical(rebuild)),
        "all_reinstantiated_local_modules": len(module_paths),
        "affected_reverse_import_modules": len(affected),
        "input_source_manifest_sha256": sha(canonical(actual_inventory)),
        "output_source_manifest_sha256": sha(canonical(after_inventory)),
        "input_files": len(originals), "output_files": len(transformed),
        "input_qrh_modules": sum(name.startswith("QRH/") and name.endswith(".lean") for name in originals),
        "output_qrh_modules": sum(name.startswith("QRH/") and name.endswith(".lean") for name in transformed),
        "changed_files": changes, "patch_sha256": sha(patch.read_bytes()),
        "stronger_literal_targets": [
            "QRH.Hecke.LFunction_ne_zero_of_slackRefined_lt_re",
            "QRH.DirichletCharacter.LFunction_ne_zero_of_slackRefined_lt_re",
            "QRH.riemannZeta_ne_zero_of_slackRefined_lt_re",
            "QRH.riemannZeta_zero_re_le_slackRefined"],
        "required_validation": [
            "Review every retuned numerical wrapper in the full analytic source chain",
            "Compile the complete candidate and its pinned dependencies in an authorized environment",
            "Check the literal all-family targets and original pole exceptions independently",
            "Inspect transitive axioms and run the independent kernel checks"],
    }
    report.write_bytes(canonical(result))
    (report.parent / "output_source_manifest.json").write_bytes(canonical(after_inventory))
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-dir", type=Path, default=PROJECT / "proofs/nielstron-20261009-tightening/compressed/formalization", help="Pinned baseline formalization directory; validated against its manifest")
    p.add_argument("--output-dir", type=Path, default=BUILD / "formalization")
    p.add_argument("--report", type=Path, default=BUILD / "source_retuning.json")
    p.add_argument("--patch", type=Path, default=BUILD / "source_retuning.patch")
    args = p.parse_args()
    result = prepare(args.source_dir.resolve(), args.output_dir.resolve(),
                     args.report.resolve(), args.patch.resolve())
    print(json.dumps({key: result[key] for key in ["status", "candidate", "strict_improvement", "input_files", "output_files", "input_qrh_modules", "output_qrh_modules"]}, indent=2))
    print("Actual ζ/t arithmetic checks: ", len(result["actual_budget_checks"]), "PASS")
    print("Changed/additional files:", len(result["changed_files"]))


if __name__ == "__main__":
    main()
