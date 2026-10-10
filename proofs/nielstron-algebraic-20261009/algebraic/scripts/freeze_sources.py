#!/usr/bin/env python3
"""Freeze a reviewed algebraic source package as a patch over the exact N24 baseline.

This records source bytes only. It does not run Lean or assert mathematical acceptance.
Run only after the candidate sources have been finalized and their build has passed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from source_package import N24_MANIFEST, check_baseline, check_protected, digest, manifest, sha, source_patch

ROOT = Path(__file__).resolve().parents[2]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-formalization", required=True, type=Path)
    parser.add_argument("--candidate-formalization", type=Path, default=ROOT / "compressed/formalization")
    parser.add_argument("--output", type=Path, default=ROOT / "algebraic")
    args = parser.parse_args()
    base, candidate, output = (p.resolve() for p in
                               (args.base_formalization, args.candidate_formalization, args.output))
    for source in (base, candidate):
        if output == source or source in output.parents or output in source.parents:
            parser.error("The patch output must be separate from both source packages")
    before, after = manifest(base), manifest(candidate)
    check_baseline(before)
    protected = check_protected(before, after)
    patch, changes = source_patch(base, candidate, before, after)
    if not changes:
        raise ValueError("The candidate is identical to the N24 baseline")
    parameters = {
        "schema_version": 1,
        "name": "Exact algebraic QRH endpoint",
        "sources_only": True,
        "lean_verification_performed": False,
        "baseline": {
            "name": "Verified N24 rational tightening",
            "source_files": len(before), "source_manifest_sha256": N24_MANIFEST,
            "replay_tool": "tools/reproduce_tightened.py",
            "parameters": "tightening/parameters.json",
        },
        "bound": {
            "theta": "11/12 - e/4",
            "e_definition": "the unique real root in [1/6, 1/5]",
            "polynomial_coefficients_descending": [657, -954, 21, 20],
            "root_interval": ["1/6", "1/5"],
            "certificate_interval": ["1/6", "167/1000"],
            "certified_strict_theta_lower": "874957019420098946128603850561452982/10^36",
            "certified_strict_theta_upper": "874957019420098946128603850561452983/10^36",
        },
        "patch": "algebraic.patch", "patch_sha256": sha(patch),
        "source_files": len(after), "source_manifest_sha256": digest(after), "files": after,
        "protected_files": protected, "changes": changes,
        "validation": "Source replay is separate from native Lean and independent kernel verification.",
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "algebraic.patch").write_bytes(patch)
    (output / "parameters.json").write_text(json.dumps(parameters, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: parameters[key] for key in
                      ("source_files", "source_manifest_sha256", "patch_sha256")}, indent=2))
    print(f"Changed source files: {len(changes)}")


if __name__ == "__main__":
    main()
