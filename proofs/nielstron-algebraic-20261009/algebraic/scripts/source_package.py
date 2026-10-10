#!/usr/bin/env python3
"""Shared source-only manifest and patch routines for the algebraic replay."""
from __future__ import annotations

import difflib
import hashlib
import json
from pathlib import Path

N24_MANIFEST = "eeef7d35e9437ad2ad5180be09bbaecf8e0403f8c16b399b868bf21818d176ed"
PROTECTED = (
    "QRH/DirichletTargets.lean", "QRH/HeckeTargets.lean", "QRH/IndependentTargets.lean",
    "QRH/Nonvanishing.lean", "QRH/StatementParity.lean", "QRH/ZeroBounds.lean",
    "QRH/ZetaTransfer.lean",
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def manifest(directory: Path) -> dict[str, str]:
    paths = [directory / "QRH.lean", *sorted((directory / "QRH").rglob("*.lean"))]
    paths += [directory / name for name in
              ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "proof_length.py")]
    if any(path.is_symlink() for path in paths):
        raise ValueError("Source package members must be regular files, not symlinks")
    return {p.relative_to(directory).as_posix(): sha(p.read_bytes()) for p in sorted(paths)}


def digest(files: dict[str, str]) -> str:
    return sha(json.dumps(files, sort_keys=True, separators=(",", ":")).encode())


def check_baseline(files: dict[str, str]) -> None:
    if len(files) != 210 or digest(files) != N24_MANIFEST:
        raise ValueError("The source baseline is not the exact verified 210-file N24 package")


def check_protected(before: dict[str, str], after: dict[str, str]) -> dict[str, dict]:
    preserved = {}
    for name in PROTECTED:
        if before.get(name) is None or after.get(name) != before[name]:
            raise ValueError(f"Protected source changed or disappeared: {name}")
        preserved[name] = {"sha256": after[name], "unchanged": True}
    return preserved


def source_patch(base: Path, candidate: Path, before: dict[str, str],
                 after: dict[str, str]) -> tuple[bytes, list[dict]]:
    pieces = []
    changes = []
    for name in sorted(before.keys() | after.keys()):
        if before.get(name) == after.get(name):
            continue
        old = (base / name).read_text().splitlines(keepends=True) if name in before else []
        new = (candidate / name).read_text().splitlines(keepends=True) if name in after else []
        pieces.append(f"diff --git a/{name} b/{name}\n")
        if name not in before:
            pieces.append("new file mode 100644\n")
        elif name not in after:
            pieces.append("deleted file mode 100644\n")
        for line in difflib.unified_diff(old, new,
                fromfile=f"a/{name}" if name in before else "/dev/null",
                tofile=f"b/{name}" if name in after else "/dev/null", n=3):
            pieces.append(line if line.endswith("\n") else line + "\n\\ No newline at end of file\n")
        changes.append({"path": name, "before_sha256": before.get(name), "after_sha256": after.get(name)})
    return "".join(pieces).encode(), changes
