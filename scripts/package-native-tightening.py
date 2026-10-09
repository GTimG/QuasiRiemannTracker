#!/usr/bin/env python3
"""Publish the reviewed native-Lean source snapshot after its final gate passes.

This packages existing evidence; it does not perform or claim an independent
Comparator, NanoDa, or con-ron check. Use --snapshot to repackage the existing
reviewed snapshot, or --workspace PATH to refresh only its approved files.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import io
import json
import os
import tarfile
import tempfile

from publication_policy import approved_files

ROOT = Path(__file__).resolve().parents[1]
ID = "nielstron-20261009-tightening"
THETA = "874957019420098946128604623/1000000000000000000000000000"
SKIP = {".git", ".lake", "__pycache__", "upstream", "toolchains", "build", "downloads"}
AUDIT = """FinalTargetsRequired.lean TightIndependentTargets.lean TightTargetsRequired.lean
ZeroBoundsEquivalence.lean frozen-targets.sha256 actual-definition-provenance.json
applied-patches.json dependency-licenses.json selected-license-overrides.json
nested-license-notices.json local-source-attribution.json LICENSES.md pnt-LICENSE rellich-LICENSE
local-build-status.json local-build-records.json local-selected-source-graph.json
local-verification.json zero-bounds-verification.json tightening-verification.json
tightening-preparation.json tightening-coefficients.json tightening-compression.json
tightening-scaled-analysis.json tightening-reproduction.json token-counts.json compression-transformations.json
selected-source-graph.json""".split()
TOOLS = "compose_candidate.py count_lean_tokens.py prune_unused.py setup_workspace.py prepare_tightening.py reproduce_tightened.py".split()


EXPORTS = {
    "README.txt": "README.md", "NOTICE.txt": "NOTICE", "PUBLICATION.txt": "PUBLICATION.md",
    "result.json": "tightening-result.json",
    "native-lean-verification.json": "compressed/audit/tightening-verification.json",
    "build-status.json": "compressed/audit/local-build-status.json",
    "token-counts.json": "compressed/audit/token-counts.json",
    "reproduction.json": "tightening/reproduction.json",
    "TightIndependentTargets.lean": "compressed/audit/TightIndependentTargets.lean",
    "TightTargetsRequired.lean": "compressed/audit/TightTargetsRequired.lean",
    "TighterNonvanishing.lean": "compressed/formalization/QRH/TighterNonvanishing.lean",
    "gate.log": "compressed/logs/local-tight-targets-required.log",
    "external-checker-status.json": "tightening/checker-evidence/checker-status.json",
}
PUBLIC_FILES = set(EXPORTS) | {"source-public.tar.gz", "SHA256SUMS.txt", "source-sha256.json", "collection.json"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_public_directory(public):
    """Never adopt existing download files into a newly generated collection."""
    if public.is_symlink():
        raise ValueError("Symlink in public evidence directory")
    if public.exists():
        for path in public.iterdir():
            if path.is_symlink() or not path.is_file() or path.name not in PUBLIC_FILES:
                raise ValueError("Unexpected file in public evidence directory")


def package_snapshot(root):
    """Package an explicitly reviewed list; never discover or approve new files."""
    proof = root / "proofs" / ID
    public = root / "public/proofs" / ID
    names = approved_files(proof)
    check_public_directory(public)
    if not set(EXPORTS.values()).issubset(names):
        raise ValueError("An evidence export is outside the reviewed allowlist")
    manifest = {name: sha((proof / name).read_bytes()) for name in names}
    work = root / ".work"
    work.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="publication-", dir=work) as temporary:
        stage = Path(temporary)
        archive = stage / "source-public.tar.gz"
        with archive.open("wb") as output:
            with gzip.GzipFile(fileobj=output, mode="wb", filename="", mtime=0) as zipped:
                with tarfile.open(fileobj=zipped, mode="w", format=tarfile.USTAR_FORMAT) as tar:
                    for name in names:
                        data = (proof / name).read_bytes()
                        item = tarfile.TarInfo(ID + "/" + name)
                        item.size, item.mode, item.mtime = len(data), 0o644, 0
                        tar.addfile(item, io.BytesIO(data))
        (stage / "SHA256SUMS.txt").write_text(sha(archive.read_bytes()) + "  source-public.tar.gz\n")
        for destination, name in EXPORTS.items():
            (stage / destination).write_bytes((proof / name).read_bytes())
        (stage / "source-sha256.json").write_text(json.dumps(manifest, indent=2) + "\n")
        collection = {name: sha((stage / name).read_bytes()) for name in sorted(PUBLIC_FILES - {"collection.json"})}
        (stage / "collection.json").write_text(json.dumps({"status": "verification-pending", "files": collection,
                                                           "snapshot_exports": EXPORTS}, indent=2) + "\n")
        # Validation completes before any public file is replaced.
        public.mkdir(parents=True, exist_ok=True)
        for name in sorted(PUBLIC_FILES):
            (stage / name).replace(public / name)
        (root / "proofs" / (ID + ".sha256.json")).write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"snapshot_files": len(names), "archive_sha256": collection["source-public.tar.gz"],
                      "status": "verification-pending"}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--workspace", type=Path)
    mode.add_argument("--snapshot", action="store_true", help="Repackage only the existing reviewed snapshot")
    args = parser.parse_args()
    if args.snapshot:
        package_snapshot(ROOT)
        return
    source = args.workspace.resolve()
    proof = ROOT / "proofs" / ID
    public = ROOT / "public/proofs" / ID
    # Reject stale/private files before copying or regenerating any evidence.
    reviewed_names = approved_files(proof)
    check_public_directory(public)
    report = json.loads((source / "compressed/audit/tightening-verification.json").read_text())
    assert report["status"] == "PASS" and report["threshold"] == THETA
    assert report["tighter_exact_three_targets_proved"] and report["strict_improvement_proved_in_lean"]
    assert report["original_exact_three_targets_proved"]
    build = json.loads((source / "compressed/audit/local-build-status.json").read_text())
    assert build["success"] and build["checked"] == build["closure"] == 7232
    assert not build["failed"] and not build["blocked"]
    for name, item in report["artifacts"].items():
        assert sha((source / "compressed" / name).read_bytes()) == item["sha256"], name
    metrics = json.loads((source / "compressed/audit/token-counts.json").read_text())
    assert metrics["qrh_package"]["after_tokens"] == 251464
    for row in metrics["qrh_package"]["files"]:
        if row.get("after_sha256"):
            assert sha((source / "compressed/formalization" / row["path"]).read_bytes()) == row["after_sha256"]
    replay = json.loads((source / "tightening-reproduced/reproduction.json").read_text())
    assert replay["status"] == "SOURCE_REPLAY_MATCHES_REFERENCE"
    assert replay["source_files"] == 210 and not replay["private_git_history_required"]
    proof.mkdir(parents=True, exist_ok=True)
    public.mkdir(parents=True, exist_ok=True)
    transformations = []
    copied = set()

    def copy(name, destination=None, neutralize=False):
        src = source / name
        assert src.is_file() and not src.is_symlink(), name
        raw = src.read_bytes()
        data = raw.replace(str(source).encode(), b"/work/qrh-proof") if neutralize else raw
        relative = destination or name
        if relative not in reviewed_names:
            raise ValueError("Workspace output is not in the reviewed publication allowlist")
        dst = proof / relative
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
        copied.add(relative)
        if raw != data:
            transformations.append({"path": relative, "original_sha256": sha(raw),
                                    "published_sha256": sha(data),
                                    "change": "Neutralized the local workspace prefix in runtime metadata only."})

    def tree(name, suffixes=None, neutralize=False):
        for base, directories, filenames in os.walk(source / name, followlinks=False):
            directories[:] = sorted(d for d in directories if d not in SKIP and not (Path(base) / d).is_symlink())
            for filename in sorted(filenames):
                path = Path(base) / filename
                if path.is_symlink() or (suffixes and path.suffix not in suffixes):
                    continue
                copy(path.relative_to(source).as_posix(), neutralize=neutralize)

    tree("compressed/formalization", {".lean", ".json", ".py"})
    copy("compressed/formalization/lean-toolchain")
    tree("compressed/scripts", {".py"})
    tree("compressed/inputs")
    copy("compressed/LICENSE")
    copy("compressed/LICENSE", "LICENSE")
    for name in AUDIT:
        copy("compressed/audit/" + name, neutralize=name.endswith(".json"))
    for name in ("local-final-targets-required.log", "local-zero-bounds-equivalence.log", "local-tight-targets-required.log"):
        copy("compressed/logs/" + name, neutralize=True)
    for name in TOOLS:
        copy("tools/" + name)
    tree("candidates/QRH", {".lean"})
    tree("manual/QRH", {".lean"})
    for path in sorted((source / "manual").glob("*-compression.json")):
        copy(path.relative_to(source).as_posix(), neutralize=True)
    tree("interfaces", {".lean"})
    tree("tightening/scripts", {".py"})
    tree("tightening/QRH", {".lean"})
    tree("tightening/checker-evidence", {".json"}, neutralize=True)
    tree("tightening/baseline", {".json"}, neutralize=True)
    tree("tightening/research", {".lean", ".json", ".log"}, neutralize=True)
    tree("tightening/iterations/01", {".lean", ".json", ".log"}, neutralize=True)
    copy("tightening/parameters.json")
    copy("tightening-reproduced/reproduction.json", "tightening/reproduction.json", neutralize=True)
    for name in ("compression-result.json", "tightening-result.json", "compression.patch", "tightening.patch"):
        copy(name, neutralize=name.endswith(".json"))
    # Retain dependency notices without bundling third-party source or binaries.
    licenses = json.loads((source / "compressed/audit/dependency-licenses.json").read_text())
    for repository in licenses:
        for number, notice in enumerate(repository["notices"]):
            original = source / "compressed" / notice["path"]
            if original.exists():
                assert sha(original.read_bytes()) == notice["sha256"]
                destination = "compressed/third-party-notices/" + repository["path"].rsplit("/", 1)[-1] + f"-{number}.txt"
                copy("compressed/" + notice["path"], destination)
    # This repository's upstream notice is retained verbatim alongside new attribution.
    (proof / "UPSTREAM-NOTICE").write_bytes((ROOT / "NOTICE").read_bytes())
    (proof / "publication-transformations.json").write_text(json.dumps({
        "changes": transformations,
        "source_policy": "Lean source, compiler scripts, immutable input manuscripts, and license notices retain their bytes.",
        "omitted": "No compiled objects, compiler binaries, dependency caches, upstream checkouts, or private operational histories are included. Original evidence may record hashes of omitted binaries; these are regenerated by the documented build.",
    }, indent=2) + "\n")
    # Draft README/NOTICE/PUBLICATION.md are maintained directly in the submission.
    for name in ("README.md", "NOTICE", "PUBLICATION.md"):
        assert (proof / name).is_file(), name
    expected = copied | {"README.md", "NOTICE", "PUBLICATION.md", "UPSTREAM-NOTICE",
                         "publication-transformations.json", "publication-files.json"}
    if expected != set(reviewed_names):
        raise ValueError("Workspace outputs differ from the reviewed publication allowlist")
    package_snapshot(ROOT)



if __name__ == "__main__":
    main()
