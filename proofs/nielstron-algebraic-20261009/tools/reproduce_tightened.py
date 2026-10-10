#!/usr/bin/env python3
"""Reconstruct the tightened QRH source package from the pinned public baseline.

Run tools/setup_workspace.py first to fetch the pinned tracker and tokenizer.
The default output is tightening-reproduced/formalization.  This command only
generates sources; Lean compilation and the target/axiom gates are separate.
No private Git history or prebuilt Lean artifacts are used.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def manifest(directory: Path) -> dict[str, str]:
    paths = [directory / "QRH.lean", *sorted((directory / "QRH").rglob("*.lean"))]
    paths += [directory / name for name in
              ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "proof_length.py")]
    return {p.relative_to(directory).as_posix(): sha(p.read_bytes()) for p in sorted(paths)}


def digest(files: dict[str, str]) -> str:
    return sha(json.dumps(files, sort_keys=True, separators=(",", ":")).encode())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tightening-reproduced",
                        help="Fresh candidate directory; sources are written below formalization/")
    parser.add_argument("--report", type=Path,
                        help="Final JSON report (default: OUTPUT/reproduction.json)")
    parser.add_argument("--parameters", type=Path, default=ROOT / "tightening/parameters.json")
    parser.add_argument("--compare-formalization", type=Path,
                        help="Read-only byte comparison with an existing formalization directory")
    args = parser.parse_args()
    output = args.output.resolve()
    # Publishing requires an empty destination, and may never touch the source
    # checkout, tracker, frozen live package, or this repository's ancestors.
    reserved = [(ROOT / name).resolve() for name in ("tracker", "compressed", "tools", "tightening",
                                                    "candidates", "manual", "interfaces", "lean-lean")]
    if output == ROOT or output in ROOT.parents or any(output == p or p in output.parents for p in reserved):
        parser.error("Choose a fresh standalone output outside the tracked inputs and live package")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error("--output must be absent or an empty directory")
    reference = args.compare_formalization.resolve() if args.compare_formalization else None
    if reference is not None and (reference == output or reference in output.parents or output in reference.parents):
        parser.error("Comparison input and output must be separate")
    report_path = (args.report or output / "reproduction.json").resolve()
    if report_path == ROOT or any(report_path == p or p in report_path.parents for p in reserved):
        parser.error("The report cannot overwrite tracked inputs or the live package")
    parameters = json.loads(args.parameters.read_text())
    theta = parameters["theta"]
    certificate = parameters["certificate"]
    scripts = ROOT / "tightening/scripts"
    tools_used = [Path(__file__).resolve(), ROOT / "tools/compose_candidate.py", ROOT / "tools/prepare_tightening.py",
                  ROOT / "tools/prune_unused.py", ROOT / "tools/count_lean_tokens.py",
                  scripts / "certificate_model.py", scripts / "update_certificate.py",
                  scripts / "prepare_numeric_compression.py", args.parameters.resolve(),
                  ROOT / parameters["new_final_source"], ROOT / parameters["support_asset"]]
    inputs = {p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p): sha(p.read_bytes())
              for p in tools_used}
    steps = []

    def run(script: Path, *arguments: object) -> None:
        command = [sys.executable, "-B", str(script), *map(str, arguments)]
        result = subprocess.run(command, check=True, text=True, capture_output=True)
        steps.append({"tool": script.relative_to(ROOT).as_posix(),
                      "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr})

    with tempfile.TemporaryDirectory(prefix="qrh-source-replay-") as temporary:
        work = Path(temporary)
        baseline = work / "baseline"
        result_dir = work / "result"
        formalization = result_dir / "formalization"
        evidence = result_dir / "reproduction-stages"
        evidence.mkdir(parents=True)
        run(ROOT / "tools/compose_candidate.py", "--output", baseline,
            "--report", evidence / "compression-baseline.json")
        # This small tracked helper did not exist in the upstream tracker.
        # Its bytes are copied independently of all mathematical proof sources.
        shutil.copyfile(ROOT / parameters["support_asset"], baseline / "proof_length.py")
        baseline_manifest = manifest(baseline)
        run(ROOT / "tools/prepare_tightening.py", "--base-dir", baseline,
            "--output", formalization, "--report", evidence / "tightening-preparation.json",
            "--numerator", theta["numerator"], "--denominator", theta["denominator"],
            "--sources-only")
        preparation = json.loads((evidence / "tightening-preparation.json").read_text())
        if preparation["baseline_source_manifest_sha256"] != parameters["baseline_source_manifest_sha256"]:
            raise ValueError("Configured baseline manifest does not match the verified public replay")
        run(scripts / "update_certificate.py", "--source", formalization / "QRH/Certificate.lean",
            "--output", formalization / "QRH/Certificate.lean",
            "--report", evidence / "certificate.json",
            "--numerator", theta["numerator"], "--denominator", theta["denominator"],
            "--f-margin", certificate["f_margin_numerator"] + "/" + certificate["f_margin_denominator"],
            "--source-f-margin", certificate["source_f_margin"],
            "--source-theta", parameters["original_theta"]["numerator"] + "/" + parameters["original_theta"]["denominator"],
            "--parameter-name", "tightTheta", "--source-parameter-name", certificate["source_parameter_name"])
        shutil.copyfile(ROOT / parameters["new_final_source"], formalization / "QRH/TighterNonvanishing.lean")
        entrypoint = formalization / "QRH.lean"
        entrypoint.write_text("import QRH.TighterNonvanishing\n" + entrypoint.read_text())
        overrides = work / "numeric-overrides"
        run(scripts / "prepare_numeric_compression.py", "--source", formalization,
            "--output", overrides, "--report", evidence / "numeric-compression.json")
        compression = json.loads((evidence / "numeric-compression.json").read_text())
        for row in compression["files"]:
            target = formalization / row["path"]
            candidate = overrides / row["path"]
            if sha(target.read_bytes()) != row["before_sha256"] or sha(candidate.read_bytes()) != row["after_sha256"]:
                raise ValueError(f"Numeric compression hash mismatch: {row['path']}")
            shutil.copyfile(candidate, target)
        budget_changes = []
        for name, replacements in parameters["budget_denominator_changes"].items():
            path = formalization / "QRH" / name
            source = path.read_text()
            seen: Counter = Counter()
            pattern = re.compile(r"(?<![0-9])(?:" + "|".join(re.escape(s) for s in replacements) + r")(?![0-9])")

            def replace_budget(match: re.Match[str]) -> str:
                old = match.group()
                seen[old] += 1
                return replacements[old]["replace_with"]

            changed = pattern.sub(replace_budget, source)
            for old, replacement in replacements.items():
                if seen[old] != replacement["occurrences"]:
                    raise ValueError(f"Budget replacement count mismatch: {name}: {old}: {seen[old]}")
            path.write_text(changed)
            budget_changes.append({"path": "QRH/" + name, "before_sha256": sha(source.encode()),
                                   "after_sha256": sha(changed.encode()), "replacements": replacements})
        geometry = formalization / "QRH/Geometry.lean"
        source = geometry.read_text()
        old_zeta = "def zeta : ℝ := 1 / " + parameters["zeta"]["old_denominator"]
        new_zeta = "def zeta : ℝ := 1 / " + parameters["zeta"]["denominator"]
        if source.count(old_zeta + "\n") != 1:
            raise ValueError("The original zeta definition does not match")
        geometry.write_text(source.replace(old_zeta + "\n", new_zeta + "\n"))
        files = manifest(formalization)
        preserved = {}
        for name in parameters["protected_files"]:
            if files[name] != baseline_manifest[name]:
                raise ValueError(f"Protected source changed during replay: {name}")
            preserved[name] = {"sha256": files[name], "unchanged": True}
        comparison = None
        if reference is not None:
            reference_files = manifest(reference)
            differences = [name for name in sorted(files.keys() | reference_files.keys())
                           if files.get(name) != reference_files.get(name)]
            comparison = {"reference": str(reference), "files_checked": len(files),
                          "byte_identical": not differences, "different_paths": differences,
                          "reference_manifest_sha256": digest(reference_files)}
            if differences:
                raise ValueError(f"Replayed sources differ from reference: {differences}")
        report = {
            "status": "SOURCE_REPLAY_MATCHES_REFERENCE" if reference else "SOURCE_REPLAY_COMPLETE",
            "sources_only": True, "lean_verification_performed": False,
            "private_git_history_required": False,
            "output": str(output), "formalization": str(output / "formalization"),
            "parameters": parameters, "input_sha256": inputs,
            "public_tracker_commit": parameters["tracker_commit"],
            "baseline_source_manifest_sha256": preparation["baseline_source_manifest_sha256"],
            "source_files": len(files), "source_manifest_sha256": digest(files), "files": files,
            "protected_files": preserved, "numeric_compression_saved_tokens": compression["saved_tokens"],
            "budget_changes": budget_changes, "comparison": comparison, "steps": steps,
        }
        shutil.copytree(result_dir, output, dirs_exist_ok=True)
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("status", "source_files", "source_manifest_sha256", "numeric_compression_saved_tokens")}, indent=2))
    print(f"Source package: {output / 'formalization'}")
    print(f"Report: {report_path}")


if __name__ == "__main__":
    main()
