"""Local multi-kernel verification; this does not submit to any registry.

The pinned Palomar helper source remains unchanged. Local wrappers add resource
ceilings, persist transcripts, and use official Comparator's own kernel sandbox
mode to avoid a nested-sandbox host-policy incompatibility. No sandbox-disable
flag or host security-policy change is used.
"""
from pathlib import Path
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

ROOT = Path(__file__).resolve().parent
PROOF = ROOT.parent / "zeta-formalization"
OLD = Path("$LEAN_4341")
JUDGE = ROOT / "tools/lean-4.35.0-rc2-linux"
PALOMAR = ROOT / "tools/palomar"
EXPORTER = ROOT / "tools/lean4export/.lake/build/bin/lean4export"
REPORT_HASH = "db64d946cc6f18787d40f66cce22603ab23277b516f23ab578cf22118b874a1a"
RUN_ID = sys.argv[1] if len(sys.argv) == 2 else "run-001"
if not re.fullmatch(r"run-[0-9]{3}", RUN_ID):
    raise SystemExit("Expected one fresh run ID, such as run-001")
WORK = ROOT / "runs" / RUN_ID
WORK.mkdir()
shutil.copyfile(Path(__file__), WORK / "runner.py")
shutil.copyfile(ROOT / "native_judge.py", WORK / "native_judge.py")
START = time.monotonic()
sys.path.insert(0, str(PALOMAR))
from scripts import verify_submission as v
from native_judge import judge_exports as native_judge_exports

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def write_json(path, record):
    path.write_text(json.dumps(record, indent=2) + "\n")

def status(phase, **extra):
    v._RESOURCE_PHASE = phase
    record = {"run": RUN_ID, "phase": phase,
              "updated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "elapsed_seconds": round(time.monotonic() - START, 3), **extra}
    write_json(WORK / "status.json", record)
    write_json(ROOT / "verification-status.json", record)
    print(json.dumps(record), flush=True)

def verify_proof_snapshot():
    report_path = PROOF / "evidence/analytic-verification-report.json"
    if digest(report_path) != REPORT_HASH:
        raise RuntimeError("Ordinary-Lean verification report changed")
    report = json.loads(report_path.read_text())
    if not report["passed"] or not report["complete_new_endpoint"]:
        raise RuntimeError("Prior proof verification was not complete")
    for item in report["sources"] + report["artifacts"]:
        path = PROOF / item["path"]
        if path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
            raise RuntimeError(f"Previously verified proof input changed: {path}")
    return report

# Preserve the upstream API behavior, adding only tighter local resource limits.
RESOURCE_PROPERTIES = ("MemoryHigh=28G", "MemoryMax=32G", "MemorySwapMax=1G", "CPUQuota=400%")
original_sandboxed_run = v.sandboxed_run
def bounded_run(*args, **kwargs):
    kwargs["resource_properties"] = (*kwargs.get("resource_properties", ()), *RESOURCE_PROPERTIES)
    return original_sandboxed_run(*args, **kwargs)
v.sandboxed_run = bounded_run

# The upstream preflight otherwise discards successful judge transcripts.
def recorded_judge_exports(**kwargs):
    proc = native_judge_exports(**kwargs, verifier=v)
    log_path = kwargs["scratch"].parent / (kwargs["scratch"].name + ".log")
    log_path.write_text(proc.stdout + "\n" + proc.stderr)
    write_json(log_path.with_suffix(".outcome.json"), {"returncode": proc.returncode,
        "transcript_sha256": digest(log_path)})
    return proc
v.judge_exports = recorded_judge_exports

ENDPOINTS = '''namespace SinglePrime2933
open scoped _root_.DirichletCharacter
theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  DIRICHLET_PROOF

theorem zeta {s : ℂ} (hs : (29 / 33 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  ZETA_PROOF

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  HECKE_PROOF
end SinglePrime2933
'''

def sources():
    # Freeze the independently proved Appendix D.3 statement verbatim. Its
    # Challenge imports definitions/presentation only, not AppendixD3 itself.
    appendix = (PROOF / "ZetaZeroFree/Analytic/Moments/AppendixD3.lean").read_text()
    header = appendix.split("theorem mixed_plain_moment_radical ", 1)[1].split(" := by", 1)[0]
    prelude = '''namespace SinglePrime2933
noncomputable section
universe u
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open ZetaZeroFree.Analytic.Moments.D3
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CanonicalRowCompletion CanonicalQuadraticSieve Filter
local notation "O" => HeckeFamily.O
'''
    moment = prelude + "theorem appendixD3 " + header + " := by\n  MOMENT_PROOF\nend\nend SinglePrime2933\n"
    statements = ENDPOINTS + "\n" + moment
    challenge = '''import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import ZetaZeroFree.Analytic.Moments.CompactProfiles
import ZetaZeroFree.Analytic.Moments.Presentation

'''
    challenge += statements
    solution = "import ZetaZeroFree.Analytic.Final\n\n" + statements
    proofs = {
        "DIRICHLET_PROOF": "exact ZetaZeroFree.Analytic.dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re χ hs hpole",
        "ZETA_PROOF": "exact ZetaZeroFree.Analytic.riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re hs hpole",
        "HECKE_PROOF": "exact ZetaZeroFree.Analytic.heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re χ hs hpole",
        "MOMENT_PROOF": "exact ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical a b B L Mcap ε Cν ha hB hM hε",
    }
    for key, proof in proofs.items():
        challenge = challenge.replace(key, "sorry")
        solution = solution.replace(key, proof)
    return {"Challenge": challenge, "Solution": solution}

def main():
    status("verify-frozen-proof-inputs", status="running")
    report = verify_proof_snapshot()
    pins = json.loads((ROOT / "pins.json").read_text())
    for name, revision in (("palomar", pins["palomar_commit"]), ("lean4export", pins["exporter_commit"])):
        actual = subprocess.check_output(["git", "-C", str(ROOT / "tools" / name), "rev-parse", "HEAD"], text=True).strip()
        if actual != revision:
            raise RuntimeError(f"Tool source pin changed: {name}")
    bwrap = v.configure_bwrap(Path("/usr/bin/bwrap"))
    v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, "memory_high_percent": 22,
        "memory_max_percent": 25, "tasks_max": 512, "open_files_max": 65536,
        "file_size_max_bytes": 16 * 1024**3}
    v._RESOURCE_METRICS_PATH = WORK / "resources.jsonl"
    v._RESOURCE_DISK_PATH = WORK
    v.install_execution_deadline(budget_seconds=10800)
    bundled = v.toolchain_tools(JUDGE)
    tools = v.tool_snapshot([*bundled.values(), bwrap, OLD / "bin/lean", EXPORTER])
    kernels = v.protected_kernels(bundled)
    primitives = v.primitive_targets(JUDGE)
    pins.update({"binaries": v.tool_digests(bundled, bwrap),
        "proof_exporter_sha256": digest(EXPORTER), "proof_compiler_sha256": digest(OLD / "bin/lean"),
        "runner_sha256": digest(Path(__file__)), "palomar_helper_sha256": digest(PALOMAR / "scripts/verify_submission.py"),
        "native_judge_sha256": digest(ROOT / "native_judge.py"),
        "judge_mode": "official Comparator built-in sandboxes; cgroup-supervised parent; no host security change",
        "resource_properties": list(RESOURCE_PROPERTIES), "effective_limits": v.VERIFICATION_LIMITS,
        "proof_report_sha256": REPORT_HASH})
    write_json(WORK / "tool-pins.json", pins)
    env = {"PATH": str(JUDGE / "bin") + ":/usr/bin:/bin", "HOME": str(ROOT / "home"),
           "TMPDIR": str(WORK), "LANG": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1"}
    status("positive-and-negative-preflight", status="running")
    v.comparator_preflight(WORK, lean=bundled["lean"], leanexport=bundled["leanexport"],
        lake=bundled["lake"], lean_prefix=JUDGE, bwrap=bwrap, kernels=kernels,
        primitives=primitives, environment=env, executable_paths=[JUDGE, bwrap, Path("/usr")],
        tools=tools, timeout=300)
    write_json(WORK / "preflight-result.json", {"passed": True,
        "checks": ["matching proof accepted", "mismatched statement rejected", "ill-typed proof rejected"],
        "source": "unmodified pinned Palomar comparator_preflight with native sandbox-enabled Comparator launcher"})
    status("preflight-passed", status="running")
    for name in ("src", "lib", "exports", "home", "tmp"):
        (WORK / name).mkdir()
    for name, source in sources().items():
        (WORK / "src" / (name + ".lean")).write_text(source)
    names = ["SinglePrime2933." + name for name in ("allDirichlet", "zeta", "allHecke", "appendixD3")]
    config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": names,
              "definition_names": [], "permitted_axioms": sorted(v.STANDARD_AXIOMS), "external_kernels": kernels}
    write_json(WORK / "comparator.json", config)
    targets = v.comparator_export_targets(config, primitives)
    build = (PROOF / ".lake").resolve()
    libraries = [(build / "build/lib/lean").resolve(),
                 *(path.resolve() for path in sorted(build.glob("packages/*/.lake/build/lib/lean")))]
    env.update({"PATH": str(OLD / "bin") + ":/usr/bin:/bin", "HOME": str(WORK / "home"),
        "TMPDIR": str(WORK / "tmp"), "LEAN_NUM_THREADS": "2",
        "LEAN_PATH": os.pathsep.join(map(str, [WORK / "lib", *libraries, OLD / "lib/lean"]))})
    write_json(WORK / "input-inventory.json", {"sources": report["sources"], "artifacts": report["artifacts"],
        "library_roots": list(map(str, libraries)), "export_targets": targets,
        "scope": "Four selected theorem proof closures, including standalone Appendix D.3; not every unused local helper theorem."})
    for name in ("Challenge", "Solution"):
        status("compile-" + name, status="running")
        proc = v.sandboxed_run([str(OLD / "bin/lean"), "-j1", "-o", str(WORK / "lib" / (name + ".olean")), str(WORK / "src" / (name + ".lean"))],
            cwd=WORK, environment=env, writable_directories=[WORK / "lib", WORK / "home", WORK / "tmp"],
            readable_paths=[WORK / "src", *libraries, *v.system_readable_paths()],
            executable_paths=[OLD, Path("/usr")], tools=tools, timeout=600, check=False)
        (WORK / (name + "-compile.log")).write_text(proc.stdout + "\n" + proc.stderr)
        if proc.returncode:
            raise RuntimeError(f"{name} compilation failed: " + proc.stdout[-2000:] + proc.stderr[-2000:])
        status("export-" + name, status="running")
        output = WORK / "exports" / (name + ".export")
        proc = v.export_module(name, targets, output=output, leanexport=EXPORTER, cwd=WORK,
            environment=env, readable_paths=[WORK / "lib", *libraries, *v.system_readable_paths()],
            executable_paths=[OLD, EXPORTER, Path("/usr")], tools=tools, timeout=1800)
        (WORK / (name + "-export.log")).write_text(proc.stdout + "\n" + proc.stderr)
        if proc.returncode:
            raise RuntimeError(f"{name} export failed: " + proc.stderr[-2000:])
        v.verify_export(output)
    verify_proof_snapshot()
    export_pins = {name: {"bytes": (WORK / "exports" / (name + ".export")).stat().st_size,
                         "sha256": digest(WORK / "exports" / (name + ".export"))}
                   for name in ("Challenge", "Solution")}
    write_json(WORK / "export-pins.json", export_pins)
    status("comparator-and-three-kernels", status="running", exports=export_pins)
    proc = v.judge_exports(lake=bundled["lake"], config=WORK / "comparator.json",
        challenge_export=WORK / "exports/Challenge.export", solution_export=WORK / "exports/Solution.export",
        scratch=WORK / "judge", bwrap=bwrap, lean_prefix=JUDGE, environment=env, tools=tools, timeout=7200)
    log = proc.stdout + "\n" + proc.stderr
    verdict = v.comparator_verdict(proc.returncode, log)
    if verdict:
        raise verdict
    markers = [name + " kernel accepts the solution" for name in ("con-ron", "nanoda", "Lean default")]
    if "Your solution is okay!" not in log or not all(marker in log for marker in markers):
        raise RuntimeError("Judge returned without all required kernel acceptance markers")
    verify_proof_snapshot()
    v.verify_tool_snapshot(tools)
    evidence = [WORK / "src/Challenge.lean", WORK / "src/Solution.lean", WORK / "comparator.json",
                WORK / "judge.log", WORK / "tool-pins.json", WORK / "preflight-result.json",
                WORK / "export-pins.json", WORK / "input-inventory.json", WORK / "resources.jsonl"]
    evidence += [WORK / "judge/supervisor.json", WORK / "judge/execution.json",
                 WORK / "runner.py", WORK / "native_judge.py"]
    result = {"status": "PASS", "kind": "local official Comparator and three-kernel verification; no registry submission",
        "declarations": names, "theta": "29/33", "kernels": ["Lean default", "nanoda", "con-ron"],
        "preflight_passed": True, "statement_definitions_compared": True,
        "allowed_axioms": config["permitted_axioms"], "source_compiler": "4.34.1",
        "judge_toolchain": "4.35.0-rc2", "exports": export_pins,
        "scope": "Proof closures of the three nonvanishing endpoints and the standalone Appendix D.3 radical mixed moment.",
        "elapsed_seconds": round(time.monotonic() - START, 3),
        "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "evidence_sha256": {str(path.relative_to(WORK)): digest(path) for path in evidence},
        "limits": ["No Palomar registry or editorial acceptance claimed.",
                   "No independent check of unused helper theorems claimed.",
                   "Proof compiler predates current Palomar submission floor; exported proof compatibility tested directly.",
                   "Uses Comparator's built-in kernel sandboxes and cgroup limits, without Palomar's extra outer judge sandbox; host security policies unchanged.",
                   "Challenge uses pinned OpenAI and local presentation definitions beyond the registry import allowlist."]}
    write_json(WORK / "result.json", result)
    status("finished", status="PASS", result=str(WORK / "result.json"))

if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        status("stopped", status="failed", error=str(error), error_type=type(error).__name__,
               error_code=getattr(error, "code", None), detail=getattr(error, "detail", None))
        traceback.print_exc()
        raise
