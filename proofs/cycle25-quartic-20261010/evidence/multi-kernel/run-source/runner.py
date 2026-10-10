"""Check the frozen Cycle25 proof with official Comparator and three kernels.

Uses the previously installed, pinned checker tools and their own kernel
sandboxes. No host security policy is changed. No registry is contacted.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import traceback

from verification_statements import sources, NAMES

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT.parent / "zeta-multikernel-20261010"
OLD = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"
JUDGE = TOOLS / "tools/lean-4.35.0-rc2-linux"
PALOMAR = TOOLS / "tools/palomar"
EXPORTER = TOOLS / "tools/lean4export/.lake/build/bin/lean4export"
sys.path.insert(0, str(PALOMAR))
sys.path.insert(0, str(TOOLS))
from scripts import verify_submission as v
from native_judge import judge_exports


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", required=True)
    parser.add_argument("--build", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"kernels-[0-9]{3}", args.run)
    assert re.fullmatch(r"clean-[0-9]{3}", args.build)
    work = ROOT / "evidence" / args.run
    build = ROOT / "evidence" / args.build
    work.mkdir()
    started = time.monotonic()

    def status(phase, **extra):
        v._RESOURCE_PHASE = phase
        record = {"run": args.run, "phase": phase,
                  "updated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "elapsed_seconds": round(time.monotonic() - started, 3), **extra}
        write(work / "status.json", record)
        print(json.dumps(record), flush=True)

    report = json.loads((build / "result.json").read_text())
    inventory = json.loads((build / "input-inventory.json").read_text())
    assert report["passed"] is True
    frozen = {build / "result.json": digest(build / "result.json"),
              build / "input-inventory.json": report["input_inventory_sha256"]}
    for item in report["sources"]:
        frozen[build / "src" / item["path"]] = item["sha256"]
        frozen[ROOT / "formalization" / item["path"]] = item["sha256"]
    for item in report["artifacts"] + inventory["upstream_artifacts"]:
        frozen[build / item["path"]] = item["sha256"]
    package_audit = ROOT / "evidence/package-source-pins.json"
    frozen[package_audit] = digest(package_audit)
    package_rows = json.loads(package_audit.read_text())
    package_roots = {Path(p).parents[3].name: Path(p).parents[3]
                     for p in inventory["package_library_roots"]}
    for row in package_rows:
        if not row["matches"]:
            raise RuntimeError("Package revision mismatch: " + row["name"])
        for relative, expected in row["modified_file_hashes"].items():
            frozen[package_roots[row["name"]] / relative] = expected

    def verify_inputs():
        for path, expected in frozen.items():
            if digest(path) != expected:
                raise RuntimeError("Frozen input changed: " + str(path))

    try:
        status("verify-frozen-inputs", status="running")
        verify_inputs()
        for row in package_rows:
            package = package_roots[row["name"]]
            revision = subprocess.check_output(["git", "-C", str(package),
                "rev-parse", "HEAD"], text=True).strip()
            patch = subprocess.check_output(["git", "-C", str(package),
                "diff", "--binary", "HEAD"])
            if (revision != row["expected"] or
                    hashlib.sha256(patch).hexdigest() != row["diff_sha256"]):
                raise RuntimeError("Package source changed: " + row["name"])
        shutil.copyfile(package_audit, work / "package-source-pins.json")
        pins = json.loads((TOOLS / "pins.json").read_text())
        for name, revision in (("palomar", pins["palomar_commit"]),
                               ("lean4export", pins["exporter_commit"])):
            actual = subprocess.check_output(["git", "-C", str(TOOLS / "tools" / name),
                                              "rev-parse", "HEAD"], text=True).strip()
            if actual != revision:
                raise RuntimeError("Checker source pin changed: " + name)
        for name, path in (("runner.py", Path(__file__)),
                           ("verification_statements.py", Path(__file__).with_name("verification_statements.py")),
                           ("native_judge.py", TOOLS / "native_judge.py")):
            shutil.copyfile(path, work / name)
        bwrap = v.configure_bwrap(Path("/usr/bin/bwrap"))
        v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, "memory_high_percent": 22,
            "memory_max_percent": 25, "tasks_max": 512, "open_files_max": 65536,
            "file_size_max_bytes": 16 * 1024**3}
        v._RESOURCE_METRICS_PATH = work / "resources.jsonl"
        v._RESOURCE_DISK_PATH = work
        v.install_execution_deadline(budget_seconds=10800)
        bundled = v.toolchain_tools(JUDGE)
        tools = v.tool_snapshot([*bundled.values(), bwrap, OLD / "bin/lean", EXPORTER])
        kernels = v.protected_kernels(bundled)
        primitives = v.primitive_targets(JUDGE)
        properties = ("MemoryHigh=28G", "MemoryMax=32G", "MemorySwapMax=1G", "CPUQuota=400%")
        original_run = v.sandboxed_run

        def bounded_run(*pargs, **kwargs):
            kwargs["resource_properties"] = (*kwargs.get("resource_properties", ()), *properties)
            return original_run(*pargs, **kwargs)

        def recorded_judge(**kwargs):
            proc = judge_exports(**kwargs, verifier=v)
            path = kwargs["scratch"].parent / (kwargs["scratch"].name + ".log")
            path.write_text(proc.stdout + "\n" + proc.stderr)
            write(path.with_suffix(".outcome.json"), {"returncode": proc.returncode,
                  "transcript_sha256": digest(path)})
            return proc

        v.sandboxed_run = bounded_run
        v.judge_exports = recorded_judge
        pins.update({"binaries": v.tool_digests(bundled, bwrap),
            "proof_exporter_sha256": digest(EXPORTER), "proof_compiler_sha256": digest(OLD / "bin/lean"),
            "runner_sha256": digest(Path(__file__)), "palomar_helper_sha256": digest(PALOMAR / "scripts/verify_submission.py"),
            "native_judge_sha256": digest(TOOLS / "native_judge.py"),
            "judge_mode": "official Comparator built-in kernel sandboxes and cgroup-supervised parent",
            "resource_properties": list(properties), "build_report_sha256": digest(build / "result.json")})
        write(work / "tool-pins.json", pins)
        env = {"PATH": str(JUDGE / "bin") + ":/usr/bin:/bin", "HOME": str(work / "home"),
               "TMPDIR": str(work), "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1"}
        status("positive-and-negative-preflight", status="running")
        v.comparator_preflight(work, lean=bundled["lean"], leanexport=bundled["leanexport"],
            lake=bundled["lake"], lean_prefix=JUDGE, bwrap=bwrap, kernels=kernels,
            primitives=primitives, environment=env, executable_paths=[JUDGE, bwrap, Path("/usr")],
            tools=tools, timeout=300)
        write(work / "preflight-result.json", {"passed": True,
            "checks": ["matching proof accepted", "mismatched statement rejected", "ill-typed proof rejected"]})
        for name in ("src", "lib", "exports", "home", "tmp"):
            (work / name).mkdir(exist_ok=True)
        for name, source in sources().items():
            (work / "src" / (name + ".lean")).write_text(source)
        config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": NAMES,
                  "definition_names": [], "permitted_axioms": sorted(v.STANDARD_AXIOMS), "external_kernels": kernels}
        write(work / "comparator.json", config)
        targets = v.comparator_export_targets(config, primitives)
        libraries = [build / "lib", build / "upstream-lib",
                     *map(Path, inventory["package_library_roots"])]
        env.update({"PATH": str(OLD / "bin") + ":/usr/bin:/bin", "TMPDIR": str(work / "tmp"),
                    "LEAN_NUM_THREADS": "2", "LEAN_PATH": os.pathsep.join(map(str, [work / "lib", *libraries, OLD / "lib/lean"]))})
        write(work / "input-inventory.json", {"build": args.build, "build_report_sha256": digest(build / "result.json"),
            "libraries": list(map(str, libraries)), "export_targets": targets,
            "scope": "Exact quartic and rational all-Dirichlet/all-Hecke/zeta; specialized variable-kappa plain moment"})
        for name in ("Challenge", "Solution"):
            status("compile-" + name, status="running")
            proc = v.sandboxed_run([str(OLD / "bin/lean"), "-j1", "-DautoImplicit=false", "-o",
                str(work / "lib" / (name + ".olean")), str(work / "src" / (name + ".lean"))],
                cwd=work, environment=env, writable_directories=[work / "lib", work / "home", work / "tmp"],
                readable_paths=[work / "src", *libraries, *v.system_readable_paths()],
                executable_paths=[OLD, Path("/usr")], tools=tools, timeout=600, check=False)
            (work / (name + "-compile.log")).write_text(proc.stdout + "\n" + proc.stderr)
            if proc.returncode:
                raise RuntimeError(name + " compile failed: " + proc.stdout[-2000:] + proc.stderr[-2000:])
            status("export-" + name, status="running")
            output = work / "exports" / (name + ".export")
            proc = v.export_module(name, targets, output=output, leanexport=EXPORTER, cwd=work,
                environment=env, readable_paths=[work / "lib", *libraries, *v.system_readable_paths()],
                executable_paths=[OLD, EXPORTER, Path("/usr")], tools=tools, timeout=1800)
            (work / (name + "-export.log")).write_text(proc.stdout + "\n" + proc.stderr)
            if proc.returncode:
                raise RuntimeError(name + " export failed: " + proc.stderr[-2000:])
            v.verify_export(output)
        verify_inputs()
        exports = {name: {"bytes": (work / "exports" / (name + ".export")).stat().st_size,
                         "sha256": digest(work / "exports" / (name + ".export"))}
                   for name in ("Challenge", "Solution")}
        write(work / "export-pins.json", exports)
        status("comparator-and-three-kernels", status="running", exports=exports)
        proc = recorded_judge(lake=bundled["lake"], config=work / "comparator.json",
            challenge_export=work / "exports/Challenge.export", solution_export=work / "exports/Solution.export",
            scratch=work / "judge", bwrap=bwrap, lean_prefix=JUDGE, environment=env, tools=tools, timeout=7200)
        log = proc.stdout + "\n" + proc.stderr
        verdict = v.comparator_verdict(proc.returncode, log)
        if verdict:
            raise verdict
        assert "Your solution is okay!" in log
        assert all(name + " kernel accepts the solution" in log for name in ("con-ron", "nanoda", "Lean default"))
        verify_inputs()
        v.verify_tool_snapshot(tools)
        result = {"status": "PASS", "kind": "Local official Comparator and three-kernel verification; no registry admission",
            "declarations": NAMES, "theta_rational": "683505193/781250000",
            "theta_exact": "11/12-ell/4, where ell is the unique quartic root in [1/6,1/5]",
            "kernels": ["Lean default", "nanoda", "con-ron"], "preflight_passed": True,
            "statement_definitions_compared": True, "allowed_axioms": config["permitted_axioms"],
            "source_compiler": "4.34.1", "judge_toolchain": "4.35.0-rc2", "exports": exports,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "scope": "Seven displayed mathematical roots and their complete proof closures; excludes unused packet supplements",
            "host_security_settings_changed": False}
        write(work / "result.json", result)
        status("finished", status="PASS")
    except BaseException as error:
        status("stopped", status="failed", error=str(error), error_type=type(error).__name__)
        traceback.print_exc()
        raise


if __name__ == "__main__":
    main()
