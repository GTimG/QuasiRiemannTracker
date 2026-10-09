#!/usr/bin/env python3
"""Stage proof-only numeric-fact reuse without editing the active build tree.

The JSON report binds each override to the SHA-256 of its input source.  Check
those hashes before integration, and build every affected module afterward.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
WORKSPACE = Path(__file__).resolve().parents[2]


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def headers(text: str) -> list[str]:
    """Capture pre-existing top-level declaration prefixes through :=.

    All replacements below occur in local have/show proof bodies.  This adds
    a mechanical cross-check that declaration statements were not modified.
    """
    return re.findall(
        r"(?ms)^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+.*?:=",
        text,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True, help="Prepared formalization directory before numeric compression")
    parser.add_argument("--output", type=Path, default=WORKSPACE / "tightening-compression-overrides")
    parser.add_argument("--report", type=Path, default=WORKSPACE / "tightening-compression-report.json")
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    if output == source or source in output.parents or output in source.parents:
        raise ValueError("Staging output must be separate from the active source tree")
    spec = importlib.util.spec_from_file_location("qrh_metric", WORKSPACE / "tools/count_lean_tokens.py")
    assert spec and spec.loader
    metric_loader = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(metric_loader)
    metric = metric_loader.metric_module(WORKSPACE / "lean-lean")
    count = metric.count_lean_tokens_in_source

    originals = {p.relative_to(source).as_posix(): p.read_text() for p in source.rglob("*.lean")
                 if p.name == "QRH.lean" or p.relative_to(source).parts[0] == "QRH"}
    staged = dict(originals)
    edits: dict[str, list[dict]] = {}

    def replace(path: str, old: str, new: str, rule: str, expected: int = 1) -> None:
        hits = staged[path].count(old)
        if hits != expected:
            raise ValueError(f"{path}: {rule}: expected {expected} matches, found {hits}")
        staged[path] = staged[path].replace(old, new)
        edits.setdefault(path, []).append({"rule": rule, "occurrences": hits,
                                          "before": old, "after": new})

    shared_old = ("have hQRHC : 0 < QRH.C QRH.tightTheta := by\n"
                  "    rw [QRH.C_formula]; norm_num [QRH.tightTheta, QRH.b, QRH.ell]")
    shared_new = "have hQRHC := QRH.NumericFacts.C_pos"
    shared_paths = {p: s.count(shared_old) for p, s in staged.items() if shared_old in s}
    if sum(shared_paths.values()) != 13:
        raise ValueError(f"Expected 13 identical positive-C proofs, found {shared_paths}")
    for path, hits in shared_paths.items():
        replace(path, shared_old, shared_new, "reuse_C_pos", hits)

    replace("QRH/NumericFacts.lean", "\nend QRH.NumericFacts\n", """
theorem C_pos : 0 < QRH.C QRH.tightTheta := by
  rw [QRH.C_formula]; norm_num [QRH.tightTheta, QRH.b, QRH.ell]

end QRH.NumericFacts
""", "add_shared_C_pos")

    replacements = [
        ("Detector/OptimizedTransportBudget", "have hC : 0≤QRH.C QRH.tightTheta := by\n    norm_num [QRH.C,QRH.ly,QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]", "have hC := QRH.NumericFacts.C_pos.le", "reuse_C_nonneg"),
        ("PrimeRows/OptimizedNonfloorTransport", "have hhpos : 0≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]", "have hhpos : 0≤QRH.h := by linarith [QRH.NumericFacts.h_lower]", "derive_h_nonneg"),
        ("Detector/OptimizedAdaptiveSaving", "have hH : 0≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.tightTheta]", "have hH : 0≤QRH.h := by linarith [QRH.NumericFacts.h_lower]", "derive_h_nonneg"),
        ("Detector/OptimizedMixedSaving", "have hh : QRH.h≤1 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.tightTheta]", "have hh : QRH.h≤1 := by linarith [QRH.NumericFacts.h_upper]", "derive_h_le_one"),
        ("Detector/OptimizedData", "have hh:QRH.h≤1:=by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.tightTheta]", "have hh:QRH.h≤1:=by linarith [QRH.NumericFacts.h_upper]", "derive_h_le_one"),
        ("Detector/CompleteNonfloorCubeData", "have hh:QRH.h+QRH.zeta≤1:=by norm_num [QRH.h,QRH.zeta,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.tightTheta]", "have hh:QRH.h+QRH.zeta≤1:=by linarith [QRH.NumericFacts.h_zeta_upper]", "derive_h_zeta_le_one"),
        ("PrimeRows/OptimizedCubeFloorArithmetic", "have hellQRHpos : 0<QRH.ell := by norm_num [QRH.ell,QRH.tightTheta]", "have hellQRHpos := QRH.NumericFacts.ell_bounds.1", "reuse_ell_pos"),
        ("Detector/OptimizedData", "have he:0<QRH.ell:=by norm_num [QRH.ell,QRH.tightTheta]", "have he:=QRH.NumericFacts.ell_bounds.1", "reuse_ell_pos"),
        ("Detector/OptimizedBatchWidths", "have hell0 : 0<QRH.ell := by norm_num [QRH.ell,QRH.tightTheta]", "have hell0 := QRH.NumericFacts.ell_bounds.1", "reuse_ell_pos"),
        ("Detector/OptimizedFloorMargin", "have hell:0≤QRH.ell:=by norm_num [QRH.ell,QRH.tightTheta]", "have hell:=QRH.NumericFacts.ell_bounds.1.le", "reuse_ell_nonneg"),
        ("Detector/LowPenaltyAbsorption", "have hell : QRH.ell ≤ (1/5:ℝ) := by norm_num [QRH.ell, QRH.tightTheta]", "have hell := QRH.NumericFacts.ell_upper.le", "reuse_ell_upper"),
        ("Detector/ActualCubeArithmeticSaving", "div_pos (by norm_num [QRH.ell,QRH.tightTheta]) hd0", "div_pos QRH.NumericFacts.ell_bounds.1 hd0", "reuse_ell_pos"),
        ("Detector/OptimizedTransportBudget", "have hell : QRH.ell≤1 := by norm_num [QRH.ell,QRH.tightTheta]", "have hell : QRH.ell≤1 := by linarith [QRH.NumericFacts.ell_upper]", "derive_ell_le_one"),
        ("Detector/OptimizedData", "have hel:QRH.ell≤1:=by norm_num [QRH.ell,QRH.tightTheta]", "have hel:QRH.ell≤1:=by linarith [QRH.NumericFacts.ell_upper]", "derive_ell_le_one"),
        ("PrimeRows/OptimizedCubeFiniteError", "show QRH.ell≤1 by norm_num [QRH.ell,QRH.tightTheta]", "show QRH.ell≤1 by linarith [QRH.NumericFacts.ell_upper]", "derive_ell_le_one"),
        ("Detector/OptimizedMixedSaving", "have hk : (2/3:ℝ)≤QRH.kappa0 := by norm_num [QRH.kappa0,QRH.tightTheta]", "have hk : (2/3:ℝ)≤QRH.kappa0 := by linarith [QRH.NumericFacts.kappa_lower]", "derive_kappa_lower"),
        ("Detector/LowSourceScales", "show 0≤(1/6:ℝ) by norm_num [QRH.b, QRH.ell, QRH.tightTheta, QRH.lx, QRH.ly, QRH.M]", "show 0≤(1/6:ℝ) by norm_num", "remove_irrelevant_unfolds"),
    ]
    for path, old, new, rule in replacements:
        replace(f"QRH/{path}.lean", old, new, rule)

    protected = {f"QRH/{n}.lean" for n in ("Nonvanishing", "DirichletTargets", "HeckeTargets",
        "IndependentTargets", "StatementParity", "ZeroBounds", "ZetaTransfer", "TighterNonvanishing")}
    assert not protected & edits.keys()
    rows = []
    rule_counts: Counter = Counter()
    for path in sorted(edits):
        old, new = originals[path], staged[path]
        if path != "QRH/NumericFacts.lean" and "QRH.NumericFacts." in new and "import QRH.NumericFacts\n" not in new:
            new = staged[path] = "import QRH.NumericFacts\n" + new
            edits[path].append({"rule": "explicit_numericfacts_import", "occurrences": 1})
        old_headers, new_headers = headers(old), headers(new)
        if path == "QRH/NumericFacts.lean":
            assert new_headers[:-1] == old_headers and new_headers[-1].startswith("theorem C_pos ")
        else:
            assert old_headers == new_headers, f"Declaration statements changed in {path}"
        dest = output / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(new)
        for edit in edits[path]:
            rule_counts[edit["rule"]] += edit["occurrences"]
        rows.append({"path": path, "before_sha256": sha(old), "after_sha256": sha(new),
                     "before_tokens": count(old), "after_tokens": count(new),
                     "saved_tokens": count(old) - count(new),
                     "existing_declaration_headers_preserved": True, "edits": edits[path]})
    report = {
        "status": "STAGED_NOT_LEAN_VERIFIED", "source": str(source), "overrides": str(output),
        "tokenizer_commit": metric_loader.TOKENIZER_COMMIT,
        "tokenizer_sha256": metric_loader.TOKENIZER_SHA256,
        "scope": "all QRH package Lean source; package imports excluded by the pinned metric",
        "before_package_tokens": sum(count(t) for t in originals.values()),
        "after_package_tokens": sum(count(t) for t in staged.values()),
        "saved_tokens": sum(r["saved_tokens"] for r in rows),
        "changed_files": len(rows), "package_files": len(originals),
        "new_theorem": "QRH.NumericFacts.C_pos : 0 < QRH.C QRH.tightTheta",
        "existing_theorem_types": "Preserved. Only proof bodies/local have proofs and imports edited.",
        "rules": dict(sorted(rule_counts.items())),
        "protected_files": {p: {"sha256": sha(originals[p]), "unchanged": True} for p in sorted(protected)},
        "integration": "Check all before_sha256 values, copy overrides, run the source build and all target gates.",
        "files": rows,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "before_package_tokens", "after_package_tokens", "saved_tokens", "changed_files")}))


if __name__ == "__main__":
    main()
