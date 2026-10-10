#!/usr/bin/env python3
"""Reproduce LeanLeanBench token counts against the immutable tracker baseline.

Run from anywhere: python3 /home/niels/riemann/tools/count_lean_tokens.py
No third-party Python packages are needed. This measures source length only;
Lean compilation and theorem/axiom equivalence require separate verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import types
from datetime import datetime, timezone
from pathlib import Path


TRACKER_COMMIT = "290d9c5463344c3e2fab93b878f3281e77e3fd6f"
TRACKER_PREFIX = "proofs/qrh-20261009/formalization"
TOKENIZER_COMMIT = "06b3dda0b3b5c82a6a6ac9979d065ad59affb908"
TOKENIZER_PATH = "src/leanlean/metrics/tokens.py"
TOKENIZER_SHA256 = "7167627283ad810fc2b2a0007c9a61c3d2dc7a71649afe9664d0e370457d2d2b"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str, input: bytes | None = None) -> bytes:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        input=input,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def metric_module(repo: Path) -> types.ModuleType:
    """Execute the exact unmodified metric from its pinned Git object."""
    source = git(repo, "show", f"{TOKENIZER_COMMIT}:{TOKENIZER_PATH}")
    if sha256(source) != TOKENIZER_SHA256:
        raise ValueError("Pinned LeanLeanBench tokenizer SHA-256 does not match")
    module = types.ModuleType("pinned_leanlean_tokens")
    exec(compile(source, f"{TOKENIZER_COMMIT}:{TOKENIZER_PATH}", "exec"), module.__dict__)
    return module


def baseline_sources(repo: Path, metric: types.ModuleType) -> dict[str, bytes]:
    listing = git(
        repo, "ls-tree", "-r", "-z", "--format=%(objectname)%x09%(path)",
        TRACKER_COMMIT, "--", TRACKER_PREFIX,
    )
    entries: list[tuple[str, str]] = []
    for entry in listing.split(b"\0"):
        if not entry:
            continue
        oid, raw_path = entry.split(b"\t", 1)
        path = raw_path.decode("utf-8").removeprefix(TRACKER_PREFIX + "/")
        if metric._metric_git_path_in_scope(path, [], ""):
            entries.append((oid.decode("ascii"), path))
    if not entries:
        raise ValueError("No Lean source files found in pinned tracker tree")
    batch = git(repo, "cat-file", "--batch", input=(
        "\n".join(oid for oid, _ in entries) + "\n"
    ).encode("ascii"))
    result: dict[str, bytes] = {}
    offset = 0
    for oid, path in entries:
        end = batch.index(b"\n", offset)
        header = batch[offset:end].decode("ascii").split()
        if header[:2] != [oid, "blob"]:
            raise ValueError(f"Unexpected Git object for {path}: {header}")
        size = int(header[2])
        result[path] = batch[end + 1:end + 1 + size]
        offset = end + 2 + size
    return result


def counts(sources: dict[str, bytes], metric: types.ModuleType) -> dict[str, dict]:
    return {
        path: {
            "tokens": metric.count_lean_tokens_in_source(data.decode("utf-8", errors="replace")),
            "sha256": sha256(data),
        }
        for path, data in sorted(sources.items())
    }


def totals(before: int, after: int) -> dict:
    return {
        "before_tokens": before,
        "after_tokens": after,
        "saved_tokens": before - after,
        "reduction_percent": 100.0 * (before - after) / before if before else 0.0,
        "after_over_before": after / before if before else None,
    }


def make_report(workspace: Path, candidate: Path) -> dict:
    metric = metric_module(workspace / "lean-lean")
    tracker = workspace / "tracker"
    baseline = counts(baseline_sources(tracker, metric), metric)
    candidate_formalization = candidate / "formalization"
    candidate_sources = {
        path.relative_to(candidate_formalization).as_posix(): path.read_bytes()
        for path in metric._iter_metric_files(candidate_formalization, [], "")
    }
    after = counts(candidate_sources, metric)
    if not after:
        raise ValueError("Candidate has no counted Lean source files")

    fixed_inputs = {}
    for name in ("lake-manifest.json", "lean-toolchain", "lakefile.lean"):
        original = git(tracker, "show", f"{TRACKER_COMMIT}:{TRACKER_PREFIX}/{name}")
        current = (candidate_formalization / name).read_bytes()
        if current != original:
            raise ValueError(f"Fixed dependency input changed: {name}")
        fixed_inputs[name] = {"sha256": sha256(original), "unchanged": True}
    manifest = json.loads((candidate_formalization / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")

    graph_git_path = "proofs/qrh-20261009/audit/selected-source-graph.json"
    graph_raw = git(tracker, "show", f"{TRACKER_COMMIT}:{graph_git_path}")
    graph = json.loads(graph_raw)
    supporting = []
    fixed_dependency_sources = 0
    for module, entry in sorted(graph.items()):
        if module == "QRH" or module.startswith("QRH."):
            continue
        source_path = candidate / entry["source"]
        data = source_path.read_bytes()
        if sha256(data) != entry["sha256"]:
            raise ValueError(f"Fixed supporting source changed: {entry['source']}")
        if module != "OAI" and not module.startswith("OAI."):
            fixed_dependency_sources += 1
            continue
        supporting.append({
            "module": module,
            "path": entry["source"],
            "sha256": entry["sha256"],
            "tokens": metric.count_lean_tokens_in_source(data.decode("utf-8", errors="replace")),
        })
    if not supporting:
        raise ValueError("Selected baseline graph contains no OAI sources")
    supporting_tokens = sum(row["tokens"] for row in supporting)
    before_total = sum(row["tokens"] for row in baseline.values())
    after_total = sum(row["tokens"] for row in after.values())
    rows = []
    for path in sorted(baseline.keys() | after.keys()):
        old, new = baseline.get(path), after.get(path)
        rows.append({
            "path": path,
            "before_tokens": old["tokens"] if old else 0,
            "after_tokens": new["tokens"] if new else 0,
            "saved_tokens": (old["tokens"] if old else 0) - (new["tokens"] if new else 0),
            "before_sha256": old["sha256"] if old else None,
            "after_sha256": new["sha256"] if new else None,
            "status": "added" if old is None else "removed" if new is None else
                      "unchanged" if old["sha256"] == new["sha256"] else "modified",
        })
    return {
        "schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "metric": {
            "name": "LeanLeanBench repository Lean source tokens",
            "repository": "https://github.com/eth-sri/lean-lean",
            "commit": TOKENIZER_COMMIT,
            "path": TOKENIZER_PATH,
            "sha256": TOKENIZER_SHA256,
            "implementation": "Exact unmodified pinned Python tokenizer, loaded from Git object",
            "counts": "All non-comment, non-import source tokens, including declarations and proof statements",
            "excludes": [".lake directories", "lakefile.lean files", "non-.lean files"],
            "not_llm_tokens": True,
        },
        "baseline": {
            "repository": "https://github.com/gtimg/QuasiRiemannTracker",
            "commit": TRACKER_COMMIT,
            "path": TRACKER_PREFIX,
            "read_from": "Immutable Git blobs; baseline working tree is not used",
        },
        "candidate": {"path": str(candidate_formalization)},
        "qrh_package": {
            "scope": "Every counted Lean source in the QRH formalization package",
            "before_files": len(baseline),
            "after_files": len(after),
            **totals(before_total, after_total),
            "files": rows,
        },
        "supporting_oai": {
            "scope": "All OAI source modules in the saved baseline selected import graph",
            "baseline_graph_git_path": graph_git_path,
            "baseline_graph_commit": TRACKER_COMMIT,
            "baseline_graph_sha256": sha256(graph_raw),
            "upstream_commit": git(candidate / "upstream/openai-math", "rev-parse", "HEAD").decode().strip(),
            "all_files_match_baseline_graph_hashes": True,
            "file_count": len(supporting),
            **totals(supporting_tokens, supporting_tokens),
            "files": supporting,
        },
        "qrh_plus_fixed_supporting_oai": {
            "scope": "QRH source package plus unchanged baseline OAI import closure; all other fixed dependencies excluded",
            **totals(before_total + supporting_tokens, after_total + supporting_tokens),
        },
        "fixed_dependencies": {
            "inputs": fixed_inputs,
            "lean_toolchain": (candidate_formalization / "lean-toolchain").read_text().strip(),
            "mathlib_commit": mathlib["rev"],
            "baseline_graph_dependency_source_files_verified": fixed_dependency_sources,
            "all_baseline_graph_dependency_sources_unchanged": True,
            "excluded_from_both_counts": "Mathlib, Lean, RellichKondrachov, PrimeNumberTheoremAnd, and tooling dependencies",
        },
        "validity": "Source metric only: compilation, preserved theorem statements, and axioms must be checked separately; this is not an official benchmark submission.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--candidate", type=Path, help="Candidate root containing formalization/ and audit/")
    parser.add_argument("--output", type=Path, help="JSON destination (default: candidate/audit/token-counts.json)")
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    candidate = (args.candidate or workspace / "compressed").resolve()
    output = (args.output or candidate / "audit/token-counts.json").resolve()
    report = make_report(workspace, candidate)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({
        "report": str(output),
        "qrh_package": {key: value for key, value in report["qrh_package"].items() if key != "files"},
        "qrh_plus_fixed_supporting_oai": report["qrh_plus_fixed_supporting_oai"],
    }, indent=2))


if __name__ == "__main__":
    main()
