#!/usr/bin/env python3
"""Judge a frozen algebraic-endpoint proof with the pinned Palomar export/checker pipeline.

This is a local independent-kernel check, not a Palomar registry admission.
Frozen proof sources and checker implementations are never modified.  Existing
source-build artifacts are hash-checked, then fresh Challenge/Solution wrappers
are compiled with Lean 4.34.1 and exported with its matching lean4export.  The
4.35.0-rc2 comparator and its three kernels judge only protected NDJSON exports.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[1]
PALOMAR_COMMIT = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
EXPORTER_COMMIT = "076e8e57707e813375e8f9da8bf989799ace9680"
SOURCE_LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
BWRAP_SHA256 = "bb807d18eaee5dad15afd5cf48c8de1c3206ff97e852af693d679d62394eb5a2"
VERIFIER_SHA256 = "c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2"
BASELINE_BUILD_INPUTS_SHA256 = "38cef2b708ec35bf5a5192addbc87ce9529c3e44ca0886123027e1732f9d6809"
BASELINE_GRAPH_SHA256 = "7364b78eb62004edfe9d7c3ebacd0b4f8cbc65f53e07dd6200816a92338cca7e"
BASELINE_RECORDS_SHA256 = "530332d9c117d87456183de122ac4fc685661f0d7aa671253d91d31bd9018b00"
DEPENDENCY_PINS = {
    "formalization/.lake/packages/mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
    "upstream/openai-math": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
}
DEFINITION_PINS = {
    "formalization/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean":
        "7ef38fb53f462e19dfd6746fc1826423e55bb5e2672c2b5667e2fd4889f401b6",
    "formalization/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean":
        "8d24b729a30f1fef0820f0f7c9cdbb5910df30dfac2c597eb666794bead08b1c",
    "upstream/openai-math/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean":
        "9871d175749b34ec40cf66ccc14b4faa0a9ef08831cb3fa901c944e57c7b9ec6",
    "upstream/openai-math/lean/OAI/NumberTheory/DirichletL/Hecke/IdealBridge.lean":
        "6c1fc33b7372108323bf3af3d4ab6f6e454ea9896b89e78964463a8e35df735f",
}
SOURCE_MANIFEST = "UNSET"
THETA = "874957019420098946128603850561452983/1000000000000000000000000000000000000"
OLD_LITERAL = "874957019421 / 1000000000000"
NEW_LITERAL = THETA.replace("/", " / ")
THEOREMS = ["QRHPalomar.allDirichlet", "QRHPalomar.zeta", "QRHPalomar.allHecke",
            "QRHPalomar.allDirichletExact", "QRHPalomar.zetaExact", "QRHPalomar.allHeckeExact", "QRHPalomar.existsUniqueRoot"]


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def git_commit(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def clean_pinned_repository(path: Path, commit: str) -> None:
    if git_commit(path) != commit:
        raise ValueError("Pinned repository commit mismatch: " + str(path))
    dirty = subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
    if dirty:
        raise ValueError("Pinned repository has changed tracked files: " + str(path))


def git_blob(checkout: Path, commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(checkout), "show", f"{commit}:{path}"])


def safe_relative(path: str) -> bool:
    return bool(path) and not Path(path).is_absolute() and ".." not in Path(path).parts and "\n" not in path


def verify_publication(checkout: Path, prefix: str, commit: str, files: dict[str, str]) -> dict:
    if not safe_relative(prefix):
        raise ValueError("Published prefix must be a relative path without parent traversal")
    resolved = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "--verify", commit + "^{commit}"], text=True).strip()
    if resolved != commit:
        raise ValueError("Published source commit did not resolve exactly")
    for name, digest in files.items():
        if not safe_relative(name):
            raise ValueError("Unsafe source manifest path: " + name)
        if hashlib.sha256(git_blob(checkout, commit, prefix.rstrip("/") + "/" + name)).hexdigest() != digest:
            raise ValueError("Published Git blob differs from checked source: " + name)
    return {"commit": commit, "prefix": prefix, "manifest_files_matched_to_git_blobs": len(files),
            "push_or_remote_availability_checked": False}


def verify_definition_pins(candidate: Path) -> dict:
    for name, commit in DEPENDENCY_PINS.items():
        clean_pinned_repository(candidate / name, commit)
    for name, digest in DEFINITION_PINS.items():
        repository = next(root for root in DEPENDENCY_PINS if name.startswith(root + "/"))
        relative = name[len(repository) + 1:]
        blob = git_blob(candidate / repository, DEPENDENCY_PINS[repository], relative)
        if sha(candidate / name) != digest or hashlib.sha256(blob).hexdigest() != digest:
            raise ValueError("Protected statement definition differs from pinned Git blob: " + name)
    return {"repositories": DEPENDENCY_PINS, "protected_definition_files": DEFINITION_PINS,
            "tracked_worktrees_clean": True, "git_blobs_matched": True}


def verify_challenge_inventory(graph: dict, records: dict, closure: set[str]) -> dict:
    evidence_path = HERE / "runs/candidate-n24-r2/build-inputs.json"
    baseline = WORKSPACE / "compressed/audit"
    graph_path = baseline / "local-selected-source-graph.json"
    records_path = baseline / "local-build-records.json"
    if (sha(evidence_path) != BASELINE_BUILD_INPUTS_SHA256
            or sha(graph_path) != BASELINE_GRAPH_SHA256
            or sha(records_path) != BASELINE_RECORDS_SHA256):
        raise ValueError("Accepted N24 Challenge provenance evidence changed")
    evidence = json.loads(evidence_path.read_text())
    if (evidence["status"] != "PASS" or evidence["source_graph_sha256"] != BASELINE_GRAPH_SHA256
            or evidence["build_records_sha256"] != BASELINE_RECORDS_SHA256):
        raise ValueError("Accepted N24 evidence is not bound to the pinned source/artifact inventories")
    baseline_graph = json.loads(graph_path.read_text())
    baseline_records = json.loads(records_path.read_text())
    expected_closure = set()

    def visit(module: str) -> None:
        if module not in expected_closure:
            expected_closure.add(module)
            for dependency in baseline_graph[module]["imports"]:
                visit(dependency)

    for module in evidence["challenge_imports"]:
        visit(module)
    if closure != expected_closure or len(closure) != 4386:
        raise ValueError("Independent Challenge dependency closure differs from accepted N24")
    sources, artifacts = {}, {}
    for module in sorted(closure):
        if graph[module] != baseline_graph[module]:
            raise ValueError("Independent Challenge source graph differs from accepted N24: " + module)
        if records[module]["olean_sha256"] != baseline_records[module]["olean_sha256"]:
            raise ValueError("Independent Challenge artifact differs from accepted N24: " + module)
        if records[module]["mode"] != baseline_records[module]["mode"]:
            raise ValueError("Independent Challenge artifact provenance mode changed: " + module)
        sources[module] = graph[module]["sha256"]
        artifacts[module] = records[module]["olean_sha256"]
    digest = lambda values: hashlib.sha256(json.dumps(values, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"baseline_run": "candidate-n24-r2", "build_inputs_sha256": BASELINE_BUILD_INPUTS_SHA256,
            "source_graph_sha256": BASELINE_GRAPH_SHA256, "build_records_sha256": BASELINE_RECORDS_SHA256,
            "module_count": len(closure), "source_inventory_sha256": digest(sources),
            "olean_inventory_sha256": digest(artifacts), "every_source_and_artifact_matches": True,
            "trust_note": "Exact shared statement-dependency artifacts from the accepted N24 run are retained. "
                          "Official Mathlib caches are pinned, not rebuilt here; proof replay occurs in the three kernels."}


def validate_candidate(candidate: Path, work: Path, jobs: int, *,
                       published_checkout: Path, published_prefix: str, published_commit: str) -> dict:
    replay = json.loads((candidate / "audit/algebraic-reproduction.json").read_text())
    if replay["source_manifest_sha256"] != SOURCE_MANIFEST:
        raise ValueError("The candidate is not the frozen algebraic source manifest")
    if not all(safe_relative(name) for name in replay["files"]):
        raise ValueError("Unsafe path in frozen source manifest")
    required = {"QRH.lean", "lake-manifest.json", "lakefile.lean", "lean-toolchain"}
    required.update(p.relative_to(candidate / "formalization").as_posix()
                    for p in (candidate / "formalization/QRH").rglob("*.lean"))
    if not required <= replay["files"].keys():
        raise ValueError("Frozen manifest omits QRH sources or build configuration")
    actual = {name: sha(candidate / "formalization" / name) for name in replay["files"]}
    canonical = json.dumps(actual, sort_keys=True, separators=(",", ":")).encode()
    if actual != replay["files"] or hashlib.sha256(canonical).hexdigest() != SOURCE_MANIFEST:
        raise ValueError("Frozen proof source/config bytes changed")
    write_json(work / "source-inputs.json", {"manifest_sha256": SOURCE_MANIFEST, "files": actual})
    publication = verify_publication(published_checkout, published_prefix, published_commit, actual)
    definitions = verify_definition_pins(candidate)
    graph = json.loads((candidate / "audit/local-selected-source-graph.json").read_text())
    records = json.loads((candidate / "audit/local-build-records.json").read_text())
    status = json.loads((candidate / "audit/local-build-status.json").read_text())
    if not status["success"] or status["failed"] or status["blocked"] or graph.keys() != records.keys():
        raise ValueError("The native source build is incomplete")
    if not {"QRH", "QRH.AlgebraicRoot", "QRH.TighterNonvanishing"} <= graph.keys():
        raise ValueError("The native build omits required algebraic target modules")
    base_paths = [Path(p).resolve(strict=True) for p in
                  (candidate / "audit/local-lean-path.txt").read_text().strip().split(os.pathsep)]
    if not base_paths or base_paths[0] != (candidate / "build/local").resolve(strict=True):
        raise ValueError("LEAN_PATH does not start with the checked candidate build")
    config = "lean-4.34.1-local-cache-build-v1"
    keys = {}

    def key(module: str) -> str:
        if module not in keys:
            row = graph[module]
            keys[module] = hashlib.sha256((row["sha256"] + "".join(key(d) for d in row["imports"]) + config).encode()).hexdigest()
            if keys[module] != records[module]["key"]:
                raise ValueError("Build dependency key mismatch: " + module)
        return keys[module]

    def verify(module: str) -> None:
        row, record = graph[module], records[module]
        if not safe_relative(row["source"]) or not safe_relative(record["olean"]):
            raise ValueError("Unsafe source or artifact path: " + module)
        if record["mode"] not in {"local-source", "official-mathlib-cache"}:
            raise ValueError("Unknown compiled-artifact provenance mode: " + module)
        if module == "QRH" or module.startswith("QRH."):
            source_name = "QRH.lean" if module == "QRH" else module.replace(".", "/") + ".lean"
            if (record["mode"] != "local-source" or row["source"] != "formalization/" + source_name
                    or row["sha256"] != actual[source_name]):
                raise ValueError("QRH build source is not bound to the frozen manifest: " + module)
        top = module.split(".")[0]
        search_root = next((p for p in base_paths if (p / top).is_dir() or (p / (top + ".olean")).is_file()), None)
        expected_olean = None if search_root is None else search_root.joinpath(*module.split(".")).with_suffix(".olean")
        if expected_olean is None or expected_olean.resolve(strict=True) != (candidate / record["olean"]).resolve(strict=True):
            raise ValueError("LEAN_PATH resolves a different artifact than the checked build: " + module)
        if sha(candidate / row["source"]) != row["sha256"]:
            raise ValueError("Build source hash mismatch: " + module)
        if sha(candidate / record["olean"]) != record["olean_sha256"]:
            raise ValueError("Compiled artifact hash mismatch: " + module)
        if record["mode"] == "local-source" and (candidate / record["olean"]).with_suffix(".source-key").read_text() != record["key"]:
            raise ValueError("Compiled artifact source stamp mismatch: " + module)

    for module in graph:
        key(module)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(verify, graph))
    roots = ["Mathlib.NumberTheory.LSeries.DirichletContinuation", "OAI.NumberTheory.DirichletL.Hecke.IdealBridge"]
    closure = set()

    def visit(module: str) -> None:
        if module in closure:
            return
        closure.add(module)
        for dep in graph[module]["imports"]:
            visit(dep)

    for module in roots:
        visit(module)
    if any(m == "QRH" or m.startswith("QRH.") for m in closure):
        raise ValueError("The independent Challenge dependency closure imports candidate QRH")
    challenge_inventory = verify_challenge_inventory(graph, records, closure)
    summary = {"status": "PASS", "modules_checked": len(graph),
               "qrh_modules_checked": sum(m == "QRH" or m.startswith("QRH.") for m in graph),
               "challenge_imports": roots, "challenge_closure_modules": len(closure),
               "challenge_imports_no_QRH": True,
               "source_graph_sha256": sha(candidate / "audit/local-selected-source-graph.json"),
               "build_records_sha256": sha(candidate / "audit/local-build-records.json"),
               "native_build": status, "sources_and_oleans_rehashed": True,
               "published_source_binding": publication, "definition_provenance": definitions,
               "accepted_challenge_inventory": challenge_inventory,
               "lean_path_artifacts_matched": True,
               "dependency_trust": "Pinned source graph; official Mathlib caches; OAI and QRH locally source-built."}
    write_json(work / "build-inputs.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default="candidate-algebraic")
    parser.add_argument("--candidate", type=Path, default=WORKSPACE / "compressed")
    parser.add_argument("--bwrap", type=Path, default=HERE / "tools/bubblewrap-0.12.0/build/bwrap")
    parser.add_argument("--temporary-apparmor-profile")
    parser.add_argument("--apparmor-profile-file", type=Path)
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--timeout", type=int, default=19800)
    parser.add_argument("--source-manifest", required=True)
    parser.add_argument("--published-source-commit", required=True)
    parser.add_argument("--published-checkout", required=True, type=Path)
    parser.add_argument("--published-prefix", required=True,
                        help="Path to compressed/formalization in the published Git commit")
    parser.add_argument("--wrapper-sources", required=True, type=Path)
    parser.add_argument("--wrapper-manifest", required=True)
    args = parser.parse_args()
    global SOURCE_MANIFEST
    SOURCE_MANIFEST = args.source_manifest
    if (not re.fullmatch(r"[0-9a-f]{64}", SOURCE_MANIFEST)
            or not re.fullmatch(r"[0-9a-f]{64}", args.wrapper_manifest)
            or not re.fullmatch(r"[0-9a-f]{40}", args.published_source_commit)
            or not safe_relative(args.published_prefix)):
        parser.error("Expected frozen source SHA256 and source commit SHA1")
    if not re.fullmatch(r"[a-z0-9_-]+", args.run_id) or not 1 <= args.jobs <= 16:
        parser.error("Use a simple run ID and 1-16 workers")
    work = HERE / "runs" / args.run_id
    work.mkdir(parents=True, exist_ok=False)
    candidate = args.candidate.resolve()
    bwrap = args.bwrap.resolve()
    source_prefix = (candidate / "toolchains/lean-4.34.1-linux").resolve()
    source_lean = source_prefix / "bin/lean"
    judge_prefix = HERE / "tools/lean-4.35.0-rc2-linux"
    exporter = HERE / "tools/lean4export/.lake/build/bin/lean4export"
    palomar = HERE / "tools/palomar"
    report = {"status": "RUNNING", "kind": "local Palomar mechanical judge; not Palomar registration",
              "started_utc": utc(), "declarations": THEOREMS, "theta": THETA,
              "kernels": ["Lean default", "nanoda", "con-ron"], "allowed_axioms": ["Classical.choice", "Quot.sound", "propext"],
              "source_manifest_sha256": SOURCE_MANIFEST,
              "published_source_commit": args.published_source_commit,
              "published_source_prefix": args.published_prefix,
              "source_compiler": "4.34.1", "judge_toolchain": "4.35.0-rc2",
              "palomar_commit": PALOMAR_COMMIT, "exporter_commit": EXPORTER_COMMIT,
              "jobs": args.jobs, "cpu_affinity": sorted(os.sched_getaffinity(0)),
              "host_policy_changed": bool(args.temporary_apparmor_profile),
              "temporary_apparmor_profile": args.temporary_apparmor_profile,
              "global_userns_restriction_unchanged": True,
              "bubblewrap_path": str(bwrap), "provisioning_performed_by_driver": False,
              "cleanup": "Temporary AppArmor profile and root-owned provisioning files removed by operator after verification.",
              "statement_definitions_compared": False, "phases": [],
              "registration_limits": ["The source compiler is older than the current Palomar submission floor; judge export compatibility is tested directly.",
                                      "Hecke statement imports pinned OpenAI definitions outside the current Palomar Challenge allowlist.",
                                      "No Palomar editorial review or registry submission is performed.",
                                      "Independent replay covers three rational targets, three exact algebraic targets, root existence/uniqueness, and their exported dependencies."]}

    def save() -> None:
        write_json(work / "result.json", report)

    def phase(name: str) -> None:
        print(f"[{utc()}] {name}", flush=True)
        report["current_phase"] = name
        report["phases"].append({"name": name, "started_utc": utc()})
        save()

    try:
        phase("validate-tools-and-frozen-build")
        clean_pinned_repository(palomar, PALOMAR_COMMIT)
        clean_pinned_repository(HERE / "tools/lean4export", EXPORTER_COMMIT)
        if sha(palomar / "scripts/verify_submission.py") != VERIFIER_SHA256:
            raise ValueError("Pinned Palomar verifier script hash mismatch")
        sys.path.insert(0, str(palomar))
        from scripts import verify_submission as v
        v.configure_bwrap(bwrap)
        v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, "memory_high_percent": 40,
                                 "memory_max_percent": 48, "tasks_max": 4096}
        report["resource_limits"] = dict(v.VERIFICATION_LIMITS)
        v.install_execution_deadline(budget_seconds=args.timeout)
        bundled = v.toolchain_tools(judge_prefix)
        pins = json.loads((HERE / "tool-pins.json").read_text())
        for name, path in bundled.items():
            if sha(path) != pins[name]["sha256"]:
                raise ValueError("Pinned judge tool hash mismatch: " + name)
        if sha(exporter) != pins["exporter"]["sha256"] or sha(bwrap) != BWRAP_SHA256:
            raise ValueError("Source exporter or provisioned bubblewrap hash mismatch")
        if sha(source_lean) != SOURCE_LEAN_SHA256:
            raise ValueError("Pinned source Lean compiler hash mismatch")
        version = subprocess.check_output([str(source_lean), "--version"], text=True).strip()
        if "version 4.34.1," not in version or "5045d0056413266e57c625dcd7c365b10e377c52" not in version:
            raise ValueError("Source compiler version mismatch")
        tools = v.tool_snapshot([*bundled.values(), source_lean, exporter, bwrap,
                                 Path(__file__), HERE / "tool-pins.json", palomar / "scripts/verify_submission.py"])
        tool_report = {"palomar_commit": PALOMAR_COMMIT, "exporter_commit": EXPORTER_COMMIT,
                       "source_compiler_version": version, "judge_tools": v.tool_digests(bundled, bwrap),
                       "source_lean_sha256": sha(source_lean), "source_exporter_sha256": sha(exporter),
                       "driver_sha256": sha(Path(__file__)),
                       "verifier_script_sha256": sha(palomar / "scripts/verify_submission.py")}
        if args.apparmor_profile_file:
            tool_report["temporary_apparmor_profile_file"] = str(args.apparmor_profile_file)
            tool_report["temporary_apparmor_profile_sha256"] = sha(args.apparmor_profile_file)
        write_json(work / "tool-pins.json", tool_report)
        validation_arguments = {"published_checkout": args.published_checkout.resolve(),
                                "published_prefix": args.published_prefix,
                                "published_commit": args.published_source_commit}
        report["native_input_validation"] = validate_candidate(candidate, work, args.jobs, **validation_arguments)
        frozen_metadata = {name: sha(candidate / name) for name in
                           ("audit/algebraic-reproduction.json", "audit/local-selected-source-graph.json",
                            "audit/local-build-records.json", "audit/local-build-status.json", "audit/local-lean-path.txt")}
        reference = args.wrapper_sources.resolve()
        expected = {name: sha(reference / name) for name in ("Challenge.lean", "Solution.lean")}
        wrapper_digest = hashlib.sha256(json.dumps(expected, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if wrapper_digest != args.wrapper_manifest:
            raise ValueError("Independent statement wrapper manifest mismatch")
        templates = {name: (reference / name).read_text() for name in expected}
        if any(hashlib.sha256(templates[name].encode()).hexdigest() != digest for name, digest in expected.items()):
            raise ValueError("Statement wrappers changed while being read")
        if re.search(r"\b(sorry|admit|axiom)\b", templates["Solution.lean"]):
            raise ValueError("Solution wrapper contains a proof hole or added axiom")
        report["reference_templates"] = expected
        report["wrapper_manifest_sha256"] = wrapper_digest
        raw_config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": THEOREMS,
                      "definition_names": [], "permitted_axioms": report["allowed_axioms"]}
        write_json(work / "requested-comparator.json", raw_config)
        kernels = v.protected_kernels(bundled)
        config = v.protected_comparator_config(work / "requested-comparator.json", work / "comparator.json", kernels=kernels)
        protected = v.validate_protected_comparator_config(config, kernels=kernels)
        challenge_module = protected["challenge_module"]
        src, library, exports = (work / name for name in ("src", "lib", "exports"))
        for directory in (src, library, exports, work / "home", work / "tmp"):
            directory.mkdir(parents=True)
        challenge_source = src / (challenge_module.replace(".", "/") + ".lean")
        challenge_source.parent.mkdir(parents=True)
        challenge_source.write_text(templates["Challenge.lean"])
        (src / "Solution.lean").write_text(templates["Solution.lean"])
        environment = {"PATH": str(source_prefix / "bin") + ":/usr/bin:/bin", "LANG": "C.UTF-8",
                       "HOME": str(work / "home"), "TMPDIR": str(work / "tmp"), "LEAN_ABORT_ON_PANIC": "1"}
        phase("positive-and-negative-checker-preflight")
        # Observe the unchanged preflight judge calls so each genuine positive
        # and negative result is retained; do not alter arguments or outcomes.
        original_judge = v.judge_exports
        controls = []

        def observe_preflight(**arguments):
            proc = original_judge(**arguments)
            label = arguments["solution_export"].stem
            log_name = "preflight-" + label + ".log"
            (work / log_name).write_text(proc.stdout + "\n" + proc.stderr)
            controls.append({"name": label, "exit_code": proc.returncode, "log": log_name})
            write_json(work / "preflight-results.json", {"cases": controls})
            return proc

        v.judge_exports = observe_preflight
        try:
            v.comparator_preflight(work, lean=bundled["lean"], leanexport=bundled["leanexport"], lake=bundled["lake"],
                                   lean_prefix=judge_prefix, bwrap=bwrap, kernels=kernels,
                                   primitives=v.primitive_targets(judge_prefix),
                                   environment={**environment, "PATH": str(judge_prefix / "bin") + ":/usr/bin:/bin"},
                                   executable_paths=[judge_prefix, bwrap, Path("/usr")], tools=tools, timeout=180)
        finally:
            v.judge_exports = original_judge
        report["palomar_preflight"] = "passed"
        report["preflight_results"] = "preflight-results.json"
        report["preflight_cases"] = {"matching_true_theorem": "accepted by all three kernels",
                                     "mismatched_statement": "rejected by comparator",
                                     "ill_typed_proof": "rejected by Lean kernel",
                                     "evidence": "Pinned comparator_preflight completed every positive and negative assertion."}
        base_paths = [Path(p) for p in (candidate / "audit/local-lean-path.txt").read_text().strip().split(os.pathsep)]
        # Candidate QRH modules are absent from this separate dependency view.
        dependencies = work / "challenge-dependencies"
        dependencies.mkdir()
        for path in base_paths[0].iterdir():
            if path.name == "QRH" or path.name.startswith("QRH."):
                continue
            (dependencies / path.name).symlink_to(path, target_is_directory=path.is_dir())
        challenge_env = {**environment, "LEAN_PATH": os.pathsep.join(map(str, [library, dependencies, *base_paths[1:]]))}
        solution_env = {**environment, "LEAN_PATH": os.pathsep.join(map(str, [library, *base_paths]))}
        readable = [work, candidate, WORKSPACE / "compressed", *v.system_readable_paths()]
        executable = [source_prefix, exporter, bwrap, Path("/usr")]
        targets = v.comparator_export_targets(protected, v.primitive_targets(judge_prefix))
        write_json(work / "export-targets.json", targets)
        for label, module, source, env in (("Challenge", challenge_module, challenge_source, challenge_env),
                                            ("Solution", "Solution", src / "Solution.lean", solution_env)):
            phase(label.lower() + "-compile")
            target = library / (module.replace(".", "/") + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            proc = v.sandboxed_run([str(source_lean), f"-j{args.jobs}", "-R", str(src), "-o", str(target), str(source)],
                                   cwd=src, environment=env, writable_directories=[library, work / "home", work / "tmp"],
                                   readable_paths=readable, executable_paths=executable, tools=tools, timeout=600, check=False)
            (work / (label + "-compile.log")).write_text(proc.stdout + "\n" + proc.stderr)
            if proc.returncode:
                raise RuntimeError(f"{label} compilation failed with exit {proc.returncode}")
            phase(label.lower() + "-export")
            destination = exports / (label.lower() + ".export")
            proc = v.export_module(module, targets, output=destination, leanexport=exporter, cwd=src,
                                   environment=env, readable_paths=readable, executable_paths=executable,
                                   tools=tools, timeout=args.timeout)
            (work / (label + "-export.log")).write_text(proc.stderr)
            if proc.returncode:
                raise RuntimeError(f"{label} export failed with exit {proc.returncode}")
            v.verify_export(destination)
            tools[destination.resolve()] = sha(destination)
            report.setdefault("exports", {})[label.lower()] = {"sha256": sha(destination), "bytes": destination.stat().st_size}
            save()
        phase("comparator-and-three-independent-kernels")
        proc = v.judge_exports(lake=bundled["lake"], config=config,
                              challenge_export=exports / "challenge.export", solution_export=exports / "solution.export",
                              scratch=work / "judge", bwrap=bwrap, lean_prefix=judge_prefix,
                              environment=environment, tools=tools, timeout=args.timeout)
        log = (proc.stdout + "\n" + proc.stderr).strip() + "\n"
        (work / "judge.log").write_text(log)
        report["judge_exit_code"] = proc.returncode
        report["comparator_exit_code"] = proc.returncode
        verdict = v.comparator_verdict(proc.returncode, log)
        if verdict is not None:
            raise verdict
        markers = ["con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
                   "Lean default kernel accepts the solution", "Your solution is okay!"]
        if any(marker not in log for marker in markers):
            raise RuntimeError("Comparator did not record every required kernel acceptance marker")
        v.verify_tool_snapshot(tools)
        # The exports must remain bound to the same current source bytes.
        current = json.loads((work / "source-inputs.json").read_text())["files"]
        if any(sha(candidate / "formalization" / p) != digest for p, digest in current.items()):
            raise ValueError("Frozen source changed during kernel verification")
        if any(sha(candidate / name) != digest for name, digest in frozen_metadata.items()):
            raise ValueError("Frozen build metadata or LEAN_PATH changed during kernel verification")
        clean_pinned_repository(palomar, PALOMAR_COMMIT)
        clean_pinned_repository(HERE / "tools/lean4export", EXPORTER_COMMIT)
        validate_candidate(candidate, work, args.jobs, **validation_arguments)
        report["frozen_build_revalidated_after_judging"] = True
        report["frozen_metadata_sha256"] = frozen_metadata
        report.update(status="PASS", statement_definitions_compared=True,
                      acceptance_markers=markers, finished_utc=utc(), verified_at_utc=utc())
        report["artifacts"] = {p.relative_to(work).as_posix(): sha(p) for p in sorted(work.rglob("*"))
                               if p.is_file() and not p.is_symlink() and p != work / "result.json"
                               and not any(part in {"challenge-dependencies", "home", "tmp", "judge", "lib", "comparator-preflight"}
                                           for part in p.relative_to(work).parts)}
        save()
        print(json.dumps({k: report[k] for k in ("status", "declarations", "theta", "kernels", "source_manifest_sha256")}, indent=2), flush=True)
        return 0
    except Exception as error:
        report.update(status="FAILED", finished_utc=utc(), error_type=type(error).__name__,
                      error=str(error), error_code=getattr(error, "code", None), detail=getattr(error, "detail", None))
        (work / "exception.log").write_text(traceback.format_exc())
        save()
        print(json.dumps(report, indent=2), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
