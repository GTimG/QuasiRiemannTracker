#!/usr/bin/env python3
"""Reconstruct the exact algebraic QRH source package from public pinned inputs.

Run tools/setup_workspace.py first. By default the unchanged N24 source replay
runs before applying the frozen algebraic patch. An exact manifest-guarded N24
source directory can instead be supplied with --base-formalization. No private
Git history, Lean binaries, compiled proofs, or checker results are required.
This command generates and checks sources only; it does not run Lean.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "algebraic/scripts"))
from source_package import N24_MANIFEST, check_baseline, check_protected, digest, manifest, sha


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "algebraic-reproduced",
                        help="Absent or empty output directory; sources go below formalization/")
    parser.add_argument("--parameters", type=Path, default=ROOT / "algebraic/parameters.json")
    parser.add_argument("--report", type=Path, help="Default: OUTPUT/reproduction.json")
    parser.add_argument("--base-formalization", type=Path,
                        help="Optional exact N24 source package; all 210 file hashes must match")
    parser.add_argument("--compare-formalization", type=Path,
                        help="Read-only byte comparison with an existing final source package")
    args = parser.parse_args()
    output = args.output.resolve()
    reserved = [(ROOT / name).resolve() for name in
                (".git", "tracker", "compressed", "tools", "algebraic", "tightening",
                 "candidates", "manual", "interfaces", "lean-lean")]
    if output == ROOT or output in ROOT.parents or any(output == p or p in output.parents for p in reserved):
        parser.error("Choose a fresh output outside the tracked inputs, tracker, and live package")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error("--output must be absent or an empty directory")
    references = [p.resolve() for p in (args.base_formalization, args.compare_formalization) if p]
    if any(p == output or p in output.parents or output in p.parents for p in references):
        parser.error("Input source packages and output must be separate")
    report_path = (args.report or output / "reproduction.json").resolve()
    if report_path == ROOT or report_path in ROOT.parents or any(
            report_path == p or p in report_path.parents for p in reserved):
        parser.error("The report cannot overwrite tracked inputs or the live package")
    if any(report_path == p or p in report_path.parents for p in references):
        parser.error("The report cannot overwrite an input source package")
    output_sources = output / "formalization"
    output_evidence = output / "reproduction-stages"
    if report_path == output or report_path in output.parents or any(
            report_path == p or p in report_path.parents for p in (output_sources, output_evidence)):
        parser.error("The report must not replace replayed sources, stage evidence, or an output directory")
    if report_path.exists():
        parser.error("The report path must not already exist")
    parameters_path = args.parameters.resolve()
    parameters = json.loads(parameters_path.read_text())
    if parameters["baseline"]["source_manifest_sha256"] != N24_MANIFEST:
        raise ValueError("Configured baseline is not the independently verified N24 package")
    patch_path = parameters_path.parent / parameters["patch"]
    if sha(patch_path.read_bytes()) != parameters["patch_sha256"]:
        raise ValueError("Algebraic source patch SHA256 mismatch")
    if parameters["source_files"] != len(parameters["files"]) or digest(parameters["files"]) != parameters["source_manifest_sha256"]:
        raise ValueError("Configured final source manifest is inconsistent")
    used = [Path(__file__).resolve(), ROOT / "algebraic/scripts/source_package.py",
            ROOT / "tools/reproduce_tightened.py", ROOT / "tightening/parameters.json",
            parameters_path, patch_path]
    inputs = {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p): sha(p.read_bytes()) for p in used}
    steps = []

    def run(command: list[str], cwd: Path | None = None) -> None:
        result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
        steps.append({"command": command, "cwd": str(cwd) if cwd else None,
                      "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode:
            raise RuntimeError(f"Source replay command failed ({result.returncode}): {result.stderr or result.stdout}")

    with tempfile.TemporaryDirectory(prefix="qrh-algebraic-replay-") as temporary:
        work = Path(temporary)
        result_dir = work / "result"
        formalization = result_dir / "formalization"
        evidence = result_dir / "reproduction-stages"
        evidence.mkdir(parents=True)
        if args.base_formalization:
            baseline = args.base_formalization.resolve()
            baseline_mode = "exact-manifest-guarded-local-N24"
        else:
            n24 = work / "n24"
            run([sys.executable, "-B", str(ROOT / "tools/reproduce_tightened.py"), "--output", str(n24)])
            baseline = n24 / "formalization"
            baseline_mode = "public-pinned-N24-source-replay"
            shutil.copyfile(n24 / "reproduction.json", evidence / "n24-reproduction.json")
            shutil.copytree(n24 / "reproduction-stages", evidence / "n24-stages")
        before = manifest(baseline)
        check_baseline(before)
        for name in before:
            destination = formalization / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(baseline / name, destination)
        run(["git", "apply", "--check", "--whitespace=nowarn", str(patch_path)], formalization)
        run(["git", "apply", "--whitespace=nowarn", str(patch_path)], formalization)
        actual_paths = {p.relative_to(formalization).as_posix() for p in formalization.rglob("*") if p.is_file()}
        if actual_paths != set(parameters["files"]):
            raise ValueError("Patched tree contains missing or unexpected source package members")
        files = manifest(formalization)
        if files != parameters["files"] or digest(files) != parameters["source_manifest_sha256"]:
            raise ValueError("Replayed algebraic package differs from its frozen source manifest")
        protected = check_protected(before, files)
        if protected != parameters["protected_files"]:
            raise ValueError("Protected source hashes differ from the frozen configuration")
        comparison = None
        if args.compare_formalization:
            reference = args.compare_formalization.resolve()
            expected = manifest(reference)
            differences = [name for name in sorted(files.keys() | expected.keys()) if files.get(name) != expected.get(name)]
            comparison = {"reference": str(reference), "files_checked": len(files), "byte_identical": not differences,
                          "different_paths": differences, "reference_manifest_sha256": digest(expected)}
            if differences:
                raise ValueError(f"Replayed sources differ from reference: {differences}")
        report = {
            "schema_version": 1,
            "status": "SOURCE_REPLAY_MATCHES_REFERENCE" if comparison else "SOURCE_REPLAY_COMPLETE",
            "sources_only": True, "lean_verification_performed": False,
            "private_git_history_required": False,
            "generated_at_utc": datetime.now(timezone.utc).isoformat(),
            "output": str(output), "formalization": str(output / "formalization"),
            "baseline_mode": baseline_mode, "baseline_source_files": len(before),
            "baseline_source_manifest_sha256": N24_MANIFEST,
            "source_files": len(files), "source_manifest_sha256": digest(files), "files": files,
            "protected_files": protected, "changes": parameters["changes"],
            "parameters": parameters, "input_sha256": inputs,
            "comparison": comparison, "steps": steps,
        }
        shutil.copytree(result_dir, output, dirs_exist_ok=True)
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("status", "source_files", "source_manifest_sha256", "baseline_mode")}, indent=2))
    print(f"Source package: {output / 'formalization'}")
    print(f"Report: {report_path}")


if __name__ == "__main__":
    main()
