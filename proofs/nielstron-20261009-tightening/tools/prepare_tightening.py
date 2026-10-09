#!/usr/bin/env python3
"""Prepare QRH sources for a strictly stronger rational bound.

The output is a formalization directory, not a bootstrapped Lean workspace.
This command only prepares sources. Regenerate Certificate.lean separately,
then rebuild and run the original and strengthened statement/axiom gates.
The compressed working tree is never used as the source baseline.
When the pinned Git commit is unavailable, --base-dir accepts a byte-identical
baseline reproduced with compose_candidate.py; its source/config manifest is
checked against the digest embedded here.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE_COMMIT = "4b0c67a3d52dcdb627d511fde29fb21864a3e034"
SOURCE_PREFIX = "compressed/formalization"
BASE_SOURCE_MANIFEST_SHA256 = "1830ca565da71dcaf512ac8a79bd853ca8532adf910d3f6fb2e4f825c1fa031e"
OLD_THETA = Fraction(874957019421, 1000000000000)
PROTECTED = {
    "QRH/Nonvanishing.lean", "QRH/DirichletTargets.lean",
    "QRH/HeckeTargets.lean", "QRH/IndependentTargets.lean",
    "QRH/StatementParity.lean", "QRH/ZeroBounds.lean",
}
PRESERVED = PROTECTED | {"QRH/ZetaTransfer.lean"}
THETA = re.compile(r"\btheta\b")
ORIGINAL_DEFINITION = "def theta : ℝ := (874957019421 / 1000000000000 : ℝ)"


def git(*args: str, data: bytes | None = None) -> bytes:
    return subprocess.run(["git", "-C", str(ROOT), *args], input=data,
                          check=True, stdout=subprocess.PIPE).stdout


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def pinned_sources() -> dict[str, bytes]:
    commit = git("rev-parse", f"{BASE_COMMIT}^{{commit}}").decode().strip()
    assert commit == BASE_COMMIT
    listing = git("ls-tree", "-r", "-z", "--format=%(objectmode)%x09%(objecttype)%x09%(objectname)%x09%(path)",
                  BASE_COMMIT, "--", SOURCE_PREFIX)
    entries = []
    for row in listing.split(b"\0"):
        if not row:
            continue
        mode, kind, oid, raw_path = row.split(b"\t", 3)
        name = raw_path.decode().removeprefix(SOURCE_PREFIX + "/")
        if kind != b"blob" or mode not in {b"100644", b"100755"}:
            raise ValueError(f"Unexpected non-regular baseline entry: {name}")
        entries.append((oid.decode(), name))
    if not entries:
        raise ValueError("Pinned formalization tree is empty")
    raw = git("cat-file", "--batch", data=("\n".join(oid for oid, _ in entries) + "\n").encode())
    result = {}
    offset = 0
    for oid, name in entries:
        end = raw.index(b"\n", offset)
        header = raw[offset:end].decode().split()
        if header[:2] != [oid, "blob"]:
            raise ValueError(f"Unexpected Git object for {name}: {header}")
        size = int(header[2])
        result[name] = raw[end + 1:end + 1 + size]
        offset = end + size + 2
    return result


def directory_sources(directory: Path) -> dict[str, bytes]:
    files = [directory / "QRH.lean"] + sorted((directory / "QRH").rglob("*.lean"))
    files += [directory / name for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain")]
    if (directory / "proof_length.py").is_file():
        files.append(directory / "proof_length.py")
    return {path.relative_to(directory).as_posix(): path.read_bytes() for path in files}


def source_manifest_digest(sources: dict[str, bytes]) -> str:
    manifest = {name: sha(data) for name, data in sorted(sources.items())
                if name.endswith(".lean") or name in {"lake-manifest.json", "lean-toolchain"}}
    return sha(json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode())


def prepare_geometry(source: str, numerator: int, denominator: int) -> str:
    matches = list(re.finditer(r"(?m)^def theta\s*:.*$", source))
    if len(matches) != 1 or matches[0].group() != ORIGINAL_DEFINITION:
        raise ValueError("Original QRH.theta definition differs from the frozen baseline")
    match = matches[0]
    additions = (
        f"\n\ndef tightTheta : ℝ := ({numerator} / {denominator} : ℝ)\n\n"
        "theorem tightTheta_lt_theta : tightTheta < theta := by\n"
        "  norm_num [tightTheta, theta]\n\n"
        "theorem tightTheta_le_theta : tightTheta ≤ theta := tightTheta_lt_theta.le\n"
    )
    result = (THETA.sub("tightTheta", source[:match.start()]) + match.group() + additions
              + THETA.sub("tightTheta", source[match.end():]))
    assert result.count(ORIGINAL_DEFINITION) == 1
    return result


def prepare_supremum(source: str) -> str:
    result = THETA.sub("tightTheta", source)
    result, count = re.subn(r"(?m)^theorem beta_le_theta\b", "theorem beta_le_tightTheta", result)
    if count != 1:
        raise ValueError("Expected exactly one original beta_le_theta proof")
    closing = "end SevenEighths.QRHFinalAssembly"
    if result.count(closing) != 1:
        raise ValueError("Supremum namespace closing is ambiguous")
    bridge = (
        "theorem beta_le_theta : beta ≤ QRH.theta :=\n"
        "  beta_le_tightTheta.trans QRH.tightTheta_le_theta\n\n"
    )
    return result.replace(closing, bridge + closing)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tightening-preview",
                        help="Output formalization directory (default: tightening-preview)")
    parser.add_argument("--report", type=Path,
                        help="JSON report (default: sibling OUTPUT-preparation.json)")
    parser.add_argument("--base-dir", type=Path,
                        help="Use a reproduced baseline formalization directory; its source/config digest must match the frozen baseline")
    parser.add_argument("--numerator", type=int, required=True)
    parser.add_argument("--denominator", type=int, required=True)
    parser.add_argument("--sources-only", action="store_true",
                        help="Explicitly select source preparation only; this is always the behavior")
    args = parser.parse_args()
    if args.denominator <= 0:
        parser.error("--denominator must be positive")
    candidate = Fraction(args.numerator, args.denominator)
    if not 0 < candidate < OLD_THETA:
        parser.error("The candidate must be positive and strictly smaller than the frozen QRH.theta")
    output = args.output.resolve()
    if output == ROOT or output == ROOT / "tracker" or ROOT / "tracker" in output.parents:
        parser.error("Choose a standalone output directory outside the repository root and tracker")
    report_path = (args.report or output.with_name(output.name + "-preparation.json")).resolve()
    base_dir = args.base_dir.resolve() if args.base_dir else None
    if base_dir is not None and (output == base_dir or base_dir in output.parents):
        parser.error("The output must be separate from --base-dir")
    sources = directory_sources(base_dir) if base_dir is not None else pinned_sources()
    manifest_digest = source_manifest_digest(sources)
    if manifest_digest != BASE_SOURCE_MANIFEST_SHA256:
        raise ValueError(f"Baseline source/config manifest differs: expected {BASE_SOURCE_MANIFEST_SHA256}, got {manifest_digest}")
    absent = PRESERVED - sources.keys()
    if absent:
        raise ValueError(f"Missing protected baseline files: {sorted(absent)}")
    transformed = {}
    changes = []
    for name, data in sources.items():
        new = data
        if name.endswith(".lean") and (name == "QRH.lean" or name.startswith("QRH/")) and name not in PRESERVED:
            source = data.decode("utf-8")
            if name == "QRH/Geometry.lean":
                text = prepare_geometry(source, args.numerator, args.denominator)
            elif name == "QRH/Detector/OptimizedSupremum.lean":
                text = prepare_supremum(source)
            else:
                text = THETA.sub("tightTheta", source)
            new = text.encode("utf-8")
        transformed[name] = new
        if new != data:
            changes.append({"path": name, "before_sha256": sha(data), "after_sha256": sha(new),
                            "original_theta_word_occurrences": len(THETA.findall(data.decode("utf-8")))})
    protected_hashes = {}
    for name in sorted(PRESERVED):
        assert transformed[name] == sources[name], name
        protected_hashes[name] = {"sha256": sha(sources[name]), "unchanged": True,
                                  "reason": "protected statement/public API" if name in PROTECTED else "legacy zeta transfer"}
    # Prepare every replacement before writing any source, so validation errors
    # cannot leave a partly transformed output tree.
    output.mkdir(parents=True, exist_ok=True)
    extras = sorted(p.relative_to(output).as_posix() for p in output.rglob("*.lean")
                    if ".lake" not in p.parts and p.relative_to(output).as_posix() not in sources)
    for name, data in transformed.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    report = {
        "status": "SOURCES_PREPARED_NOT_VERIFIED", "sources_only": True,
        "baseline_commit": BASE_COMMIT, "baseline_path": SOURCE_PREFIX,
        "baseline_source": "directory override checked against frozen manifest" if base_dir else "immutable Git blobs",
        "baseline_directory": str(base_dir) if base_dir else None,
        "baseline_source_manifest_sha256": manifest_digest,
        "baseline_source_manifest_matches_frozen": True,
        "output": str(output), "candidate": {"numerator": args.numerator, "denominator": args.denominator},
        "strictly_smaller_than_original": True,
        "original_theta_definition_preserved": ORIGINAL_DEFINITION,
        "protected_files": protected_hashes,
        "source_files_written": len(transformed), "changed_paths": [row["path"] for row in changes],
        "changes": changes, "preexisting_extra_lean_files_not_touched": extras,
        "certificate_regeneration_required": "QRH/Certificate.lean retains the old exact certificate coefficients and must be regenerated for tightTheta.",
        "required_validation": ["Regenerate the exact rational certificate", "Rebuild every QRH source with unchanged pinned dependencies",
                                "Recheck original frozen targets and axiom gate", "Add and independently check strengthened nonvanishing/zero-bound statements"],
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "output": str(output), "report": str(report_path),
                      "source_files_written": len(transformed), "changed_files": len(changes),
                      "protected_files_unchanged": len(protected_hashes)}, indent=2))


if __name__ == "__main__":
    main()
