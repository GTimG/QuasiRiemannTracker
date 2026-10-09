#!/usr/bin/env python3
"""Judge the frozen N24 proof with the pinned Palomar export/checker pipeline.

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
SOURCE_MANIFEST = "eeef7d35e9437ad2ad5180be09bbaecf8e0403f8c16b399b868bf21818d176ed"
THETA = "874957019420098946128604623/1000000000000000000000000000"
OLD_LITERAL = "874957019421 / 1000000000000"
NEW_LITERAL = THETA.replace("/", " / ")
THEOREMS = ["QRHPalomar.allDirichlet", "QRHPalomar.zeta", "QRHPalomar.allHecke"]


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def git_commit(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def validate_candidate(candidate: Path, work: Path, jobs: int) -> dict:
    replay = json.loads((candidate / "audit/tightening-reproduction.json").read_text())
    if replay["source_manifest_sha256"] != SOURCE_MANIFEST:
        raise ValueError("The candidate is not the frozen N24 source manifest")
    actual = {name: sha(candidate / "formalization" / name) for name in replay["files"]}
    canonical = json.dumps(actual, sort_keys=True, separators=(",", ":")).encode()
    if actual != replay["files"] or hashlib.sha256(canonical).hexdigest() != SOURCE_MANIFEST:
        raise ValueError("Frozen proof source/config bytes changed")
    write_json(work / "source-inputs.json", {"manifest_sha256": SOURCE_MANIFEST, "files": actual})
    graph = json.loads((candidate / "audit/local-selected-source-graph.json").read_text())
    records = json.loads((candidate / "audit/local-build-records.json").read_text())
    status = json.loads((candidate / "audit/local-build-status.json").read_text())
    if not status["success"] or status["failed"] or status["blocked"] or graph.keys() != records.keys():
        raise ValueError("The native source build is incomplete")
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
    summary = {"status": "PASS", "modules_checked": len(graph),
               "qrh_modules_checked": sum(m == "QRH" or m.startswith("QRH.") for m in graph),
               "challenge_imports": roots, "challenge_closure_modules": len(closure),
               "challenge_imports_no_QRH": True,
               "source_graph_sha256": sha(candidate / "audit/local-selected-source-graph.json"),
               "build_records_sha256": sha(candidate / "audit/local-build-records.json"),
               "native_build": status, "sources_and_oleans_rehashed": True,
               "dependency_trust": "Pinned source graph; official Mathlib caches; OAI and QRH locally source-built."}
    write_json(work / "build-inputs.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default="candidate-n24")
    parser.add_argument("--candidate", type=Path, default=WORKSPACE / "compressed")
    parser.add_argument("--bwrap", type=Path, default=HERE / "tools/bubblewrap-0.12.0/build/bwrap")
    parser.add_argument("--temporary-apparmor-profile")
    parser.add_argument("--apparmor-profile-file", type=Path)
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--timeout", type=int, default=19800)
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9_-]+", args.run_id) or not 1 <= args.jobs <= 16:
        parser.error("Use a simple run ID and 1-16 workers")
    work = HERE / "runs" / args.run_id
    work.mkdir(parents=True, exist_ok=False)
    candidate = args.candidate.resolve()
    bwrap = args.bwrap.resolve()
    source_prefix = candidate / "toolchains/lean-4.34.1-linux"
    source_lean = source_prefix / "bin/lean"
    judge_prefix = HERE / "tools/lean-4.35.0-rc2-linux"
    exporter = HERE / "tools/lean4export/.lake/build/bin/lean4export"
    palomar = HERE / "tools/palomar"
    report = {"status": "RUNNING", "kind": "local Palomar mechanical judge; not Palomar registration",
              "started_utc": utc(), "declarations": THEOREMS, "theta": THETA,
              "kernels": ["Lean default", "nanoda", "con-ron"], "allowed_axioms": ["Classical.choice", "Quot.sound", "propext"],
              "source_manifest_sha256": SOURCE_MANIFEST,
              "published_source_commit": "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6",
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
                                      "Independent replay covers the three stronger targets and their exported dependencies, not every unused QRH declaration."]}

    def save() -> None:
        write_json(work / "result.json", report)

    def phase(name: str) -> None:
        print(f"[{utc()}] {name}", flush=True)
        report["current_phase"] = name
        report["phases"].append({"name": name, "started_utc": utc()})
        save()

    try:
        phase("validate-tools-and-frozen-build")
        if git_commit(palomar) != PALOMAR_COMMIT or git_commit(HERE / "tools/lean4export") != EXPORTER_COMMIT:
            raise ValueError("Pinned verifier source commit mismatch")
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
        if sha(exporter) != pins["exporter"]["sha256"] or sha(bwrap) != sha(HERE / "tools/bubblewrap-0.12.0/build/bwrap"):
            raise ValueError("Source exporter or provisioned bubblewrap hash mismatch")
        version = subprocess.check_output([str(source_lean), "--version"], text=True).strip()
        if "version 4.34.1," not in version or "5045d0056413266e57c625dcd7c365b10e377c52" not in version:
            raise ValueError("Source compiler version mismatch")
        tools = v.tool_snapshot([*bundled.values(), source_lean, exporter, bwrap])
        tool_report = {"palomar_commit": PALOMAR_COMMIT, "exporter_commit": EXPORTER_COMMIT,
                       "source_compiler_version": version, "judge_tools": v.tool_digests(bundled, bwrap),
                       "source_lean_sha256": sha(source_lean), "source_exporter_sha256": sha(exporter),
                       "driver_sha256": sha(Path(__file__)),
                       "verifier_script_sha256": sha(palomar / "scripts/verify_submission.py")}
        if args.apparmor_profile_file:
            tool_report["temporary_apparmor_profile_file"] = str(args.apparmor_profile_file)
            tool_report["temporary_apparmor_profile_sha256"] = sha(args.apparmor_profile_file)
        write_json(work / "tool-pins.json", tool_report)
        report["native_input_validation"] = validate_candidate(candidate, work, args.jobs)
        reference = WORKSPACE / "tracker/public/proofs/palomar-20261009/qrh/src"
        expected = {"Challenge.lean": "eee59775c5f4f892199f7456f85f7664a14ef3010fc1b3df97ed2c0f8a1db4e6",
                    "Solution.lean": "6c8dcc401534bf8af9220168868467ec67d2788137133048a93d5922396eba41"}
        templates = {}
        for name, digest in expected.items():
            if sha(reference / name) != digest:
                raise ValueError("Accepted reference template hash mismatch: " + name)
            text = (reference / name).read_text()
            if text.count(OLD_LITERAL) != 3:
                raise ValueError("Expected three literal threshold occurrences")
            templates[name] = text.replace(OLD_LITERAL, NEW_LITERAL)
        templates["Solution.lean"] = templates["Solution.lean"].replace("import QRH.Nonvanishing", "import QRH.TighterNonvanishing").replace("_of_theta_lt_re", "_of_tightTheta_lt_re")
        report["reference_templates"] = expected
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
        readable = [work, candidate, *v.system_readable_paths()]
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
