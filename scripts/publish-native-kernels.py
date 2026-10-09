#!/usr/bin/env python3
"""Package an actual completed independent checker run; never run the check.

The final dossier is validated before it is installed. Existing native proof
and evidence directories are immutable and are never written by this command.
The optional catalogue update is a proposal for maintainer review, not a signed
admission receipt. A failed or incomplete source run is refused.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ID = "nielstron-20261009-tightening"
DIRECTORY = "public/proofs/nielstron-20261009-kernels"
COMMIT = "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6"
MANIFEST = "eeef7d35e9437ad2ad5180be09bbaecf8e0403f8c16b399b868bf21818d176ed"
ARCHIVE = "4388d6e63f0127ce12a116ead3ffecbdc1db2a0d33b5da15993c206c69896dd4"


def sha(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def safe(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or str(path) != name or "\\" in name:
        raise ValueError("Unsafe evidence path")
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--binary-pins", type=Path,
                        help="Flat driver input pins; defaults to tool-pins.json beside the runner")
    parser.add_argument("--workspace", type=Path, required=True,
                        help="Source workspace prefix to neutralize in runtime metadata")
    parser.add_argument("--provisioning-report", type=Path, required=True)
    parser.add_argument("--profile-evidence", type=Path, required=True)
    parser.add_argument("--cleanup-report", type=Path, required=True)
    parser.add_argument("--challenge-audit", type=Path, required=True)
    parser.add_argument("--checker-audit", type=Path, required=True)
    parser.add_argument("--propose-status", action="store_true",
                        help="Propose framework-verified metadata after all evidence validates")
    args = parser.parse_args()
    run = args.run_dir.resolve()
    target = ROOT / DIRECTORY
    if target.exists():
        raise ValueError("Independent evidence is immutable; use a new dossier for another run")
    original = json.loads((run / "result.json").read_text())
    if (original.get("status") != "PASS" or original.get("comparator_exit_code") != 0
            or original.get("palomar_preflight") != "passed"
            or original.get("published_source_commit") != COMMIT
            or original.get("source_manifest_sha256") != MANIFEST):
        raise ValueError("No completed checker acceptance for the exact submitted proof")
    for name, digest in original["artifacts"].items():
        safe(name)
        path = run / name
        if path.is_symlink() or not path.is_file() or sha(path) != digest:
            raise ValueError("Actual checker artifact changed: " + name)
    pins = json.loads((run / "tool-pins.json").read_text())
    binary_pins = args.binary_pins or args.runner.parent / "tool-pins.json"
    if sha(args.runner) != pins["driver_sha256"]:
        raise ValueError("Supplied runner is not the one used by this run")
    cleanup = json.loads(args.cleanup_report.read_text())
    if (cleanup.get("status") != "temporary_profile_and_binary_removed"
            or cleanup.get("profile_loaded") is not False
            or cleanup.get("temporary_directory_exists") is not False
            or cleanup.get("global_userns_restriction") != "1"):
        raise ValueError("Temporary sandbox provisioning has not been verifiably cleaned up")
    if sha(args.profile_evidence) != pins["temporary_apparmor_profile_sha256"]:
        raise ValueError("Retained AppArmor profile differs from the one used")
    controls = json.loads((run / original["preflight_results"]).read_text())
    if len(controls.get("cases", [])) != 3:
        raise ValueError("Missing positive or negative preflight controls")
    # Public policy excludes operational filenames; preserve the actual logs
    # under descriptive evidence names and record every path/hash mapping.
    mapping = {original["preflight_results"]: "control-results.json"}
    for control, name in zip(controls["cases"], ("matching", "mismatched", "ill-typed"), strict=True):
        mapping[control["log"]] = "controls/" + name + ".log"
    work = ROOT / ".work"
    work.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="native-kernels-", dir=work) as temporary:
        staging = Path(temporary) / "dossier"
        staging.mkdir()
        transformations = []
        workspace = str(args.workspace.resolve()).encode()

        def copy(source, destination, neutralize=True):
            safe(destination)
            data = source.read_bytes()
            published = data.replace(workspace, b"/work/qrh-proof") if neutralize else data
            out = staging / destination
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(published)
            transformations.append({"published_path": destination,
                                    "original_sha256": hashlib.sha256(data).hexdigest(),
                                    "published_sha256": hashlib.sha256(published).hexdigest(),
                                    "workspace_prefix_neutralized": data != published})

        for name in original["artifacts"]:
            if name.startswith("exports/"):
                continue
            copy(run / name, mapping.get(name, name), neutralize=not name.endswith(".lean"))
        for control in controls["cases"]:
            control["log"] = mapping[control["log"]]
        write_json(staging / "control-results.json", controls)
        copy(run / "result.json", "original-report.json")
        copy(args.runner, "verify_candidate.py", neutralize=False)
        copy(binary_pins, "checker-binary-pins.json")
        copy(args.provisioning_report, "namespace-provisioning.json")
        copy(args.profile_evidence, "temporary-apparmor-profile.txt", neutralize=False)
        copy(args.cleanup_report, "namespace-cleanup.json")
        copy(args.challenge_audit, "challenge-source-audit.json")
        copy(args.checker_audit, "checker-source-audit.json")
        report = json.loads((staging / "original-report.json").read_text())
        config = json.loads((staging / "comparator.json").read_text())
        report.update(source_commit=COMMIT, source_archive_sha256=ARCHIVE,
                      comparator_config="comparator.json", judge_log="judge.log",
                      challenge_source="src/" + config["challenge_module"].replace(".", "/") + ".lean",
                      solution_source="src/Solution.lean", preflight_results="control-results.json",
                      tool_pins="tool-pins.json", runner="verify_candidate.py")
        report["export_sizes"] = {name: (run / name).stat().st_size
                                  for name in original["artifacts"] if name.startswith("exports/")}
        report["publication_note"] = ("This is a sanitized derivative of the actual accepted run. "
                                      "Recorded outcomes, mathematical sources, tool hashes and proof-export hashes "
                                      "are unchanged. Artifact digests below authenticate published bytes. "
                                      "The original report and per-file publication transformations are retained.")
        report["artifacts"] = {p.relative_to(staging).as_posix(): sha(p)
                               for p in sorted(staging.rglob("*")) if p.is_file()}
        report["artifacts"].update({name: digest for name, digest in original["artifacts"].items()
                                   if name.startswith("exports/")})
        # The transformed controls report rewrites log paths, not outcomes.
        for item in transformations:
            item["published_sha256"] = sha(staging / item["published_path"])
        write_json(staging / "publication-transformations.json", {
            "files": transformations, "path_mapping": mapping,
            "control_report_change": "Log filenames are mapped to the retained public evidence names; cases and actual exit statuses are unchanged.",
            "omitted_exports": {name: {"sha256": original["artifacts"][name], "bytes": size}
                                for name, size in report["export_sizes"].items()},
        })
        write_json(staging / "result.json", report)
        (staging / "README.txt").write_text(
            "Independent mechanical checks for Nielstron's exact N24 refinement\n\n"
            "The recorded local Palomar mechanical run passed the fixed three-target Comparator\n"
            "comparison and Lean's fresh kernel, NanoDa, and con-ron. The positive control passed;\n"
            "the mismatched-statement and ill-typed-proof controls were rejected as required.\n"
            "Only propext, Classical.choice and Quot.sound were permitted, with no definition holes.\n\n"
            f"Checked source commit: {COMMIT}\nSource manifest SHA256: {MANIFEST}\n"
            f"Immutable source archive SHA256: {ARCHIVE}\n"
            "The source snapshot remains under proofs/nielstron-20261009-tightening. Its older\n"
            "native reports and pending labels are preserved as historical evidence. This new\n"
            "dossier records the later checker acceptance; it does not alter the proof.\n\n"
            "Independent kernel replay covers the three stronger all-Dirichlet, zeta and Hecke\n"
            "targets and their exported proof dependencies. It does not separately replay every\n"
            "unused QRH declaration, older-bound theorem or ZeroBounds implementation; those\n"
            "retain the recorded native Lean checks. The stronger targets mathematically imply\n"
            "the older bound, and both exact target families passed the native Lean gates.\n\n"
            "Lean4.34.1 and its pinned exporter produced the exports. The judge and three kernels\n"
            "are pinned Lean4.35.0-rc2 binaries. Tool hashes and runner source are retained.\n"
            "Namespace provisioning used a temporary path-specific AppArmor userns profile for\n"
            "the root-owned pinned bubblewrap binary. Proof code ran as an unprivileged user.\n"
            "Global userns restrictions were retained; provisioning and cleanup reports are included.\n\n"
            "The local result is not Palomar registration, editorial acceptance or a signed tracker\n"
            "receipt. Maintainers review catalogue status changes before publication. Source-version\n"
            "and Challenge-import restrictions for Palomar registration still apply.\n\n"
            "Reproduction: first follow the immutable proof snapshot's README. Place the retained\n"
            "verify_candidate.py under WORKSPACE/tightening-research/checkers beside tools matching\n"
            "tool-pins.json (Palomar sources, source lean4export, judge toolchain and bubblewrap).\n"
            "Copy checker-binary-pins.json to WORKSPACE/tightening-research/checkers/tool-pins.json;\n"
            "this is the driver's flat input file. The dossier's separate tool-pins.json records\n"
            "nested metadata from the accepted run and cannot substitute for that input file.\n"
            "Provision a disposable Linux worker with genuine nested sandbox support, then run\n"
            "python3 verify_candidate.py --candidate WORKSPACE/compressed --run-id fresh-check\n"
            "using --bwrap and, where applicable, the documented temporary profile options.\n"
            "Do not disable the driver's preflight or any kernel. The driver refuses existing run\n"
            "directories and audits all native source/object hashes before compiling the wrappers.\n\n"
            "Large proof exports are omitted from this website; their actual sizes and SHA256 hashes\n"
            "are retained and fresh exports can be regenerated. Workspace prefixes in runtime\n"
            "metadata/logs are neutralized. Source bytes, tool hashes and recorded outcomes remain\n"
            "unchanged. collection.json authenticates every published file; website checks verify\n"
            "evidence integrity and do not execute the mathematical checkers.\n"
        )
        (staging / "PalomarSubmission-LICENSE.txt").write_bytes(
            (ROOT / "public/proofs/palomar-20261009/PalomarSubmission-LICENSE.txt").read_bytes())
        write_json(staging / "collection.json", {
            "schema_version": 1, "kind": "local-mechanical-kernel-evidence",
            "source_commit": COMMIT,
            "files": {p.relative_to(staging).as_posix(): sha(p) for p in sorted(staging.rglob("*")) if p.is_file()},
        })
        catalogue = json.loads((ROOT / "catalogue/results.json").read_text())
        record = next(r for r in catalogue["records"] if r["id"] == ID)
        for reference in record["references"]:
            if reference["url"] == f"proofs/{ID}/external-checker-status.json":
                reference["label"] = "Historical checker setup report"
        refs = [("Independent Comparator and three-kernel report", "result.json"),
                ("Independent checker method and reproduction", "README.txt"),
                ("Independent three-kernel acceptance log", "judge.log"),
                ("Exact independent checker statements", report["challenge_source"]),
                ("Positive and negative checker controls", "control-results.json")]
        record["references"] = [{"label": label, "url": DIRECTORY.removeprefix("public/") + "/" + name}
                                for label, name in refs] + record["references"]
        if args.propose_status:
            record.update(status="framework-verified", first_verified_at=report["verified_at_utc"], source_commit=COMMIT,
                          verification_note=("The exact submitted proof passed the pinned local Palomar mechanical suite: "
                                             "Comparator compared all three statements and their definitions, then Lean's fresh kernel, "
                                             "NanoDa and con-ron accepted the exports. Matching, mismatched-statement and ill-typed-proof "
                                             "preflight controls passed. Only propext, Classical.choice and Quot.sound were permitted. "
                                             "This is a local mechanical result, proposed for maintainer review; it is not Palomar "
                                             "registration, editorial acceptance or a signed tracker receipt. Earlier native reports "
                                             "and their pending status remain immutable historical evidence."))
        candidate_catalogue = Path(temporary) / "catalogue.json"
        write_json(candidate_catalogue, catalogue)
        subprocess.run(["node", str(ROOT / "scripts/check-native-kernels.mjs"),
                        "--evidence-dir", str(staging), "--catalogue", str(candidate_catalogue)], check=True)
        # Reuse the publication policy's content checks before installing any file.
        from publication_policy import check_content
        for path in staging.rglob("*"):
            if path.is_file():
                check_content(path.relative_to(staging).as_posix(), path.read_bytes())
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(staging), target)
        text = candidate_catalogue.read_text().replace('"builds_on": [\n        "openai-baseline"\n      ],',
                                                     '"builds_on": ["openai-baseline"],')
        (ROOT / "catalogue/results.json").write_text(text)
        print(json.dumps({"dossier": DIRECTORY, "status_proposal": record["status"],
                          "verified_at_utc": report["verified_at_utc"], "source_commit": COMMIT}))


if __name__ == "__main__":
    main()
