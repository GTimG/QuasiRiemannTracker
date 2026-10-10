#!/usr/bin/env python3
"""Audit the new analytic proof with normal Lean; --core records partial progress.

The default requires the unconditional new endpoint and a fresh kernel replay.
The historical verify.py checks a different, previously completed scope.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
TOOLCHAIN = "leanprover/lean4:v4.34.1"
COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
PREFIX = ["elan", "run", TOOLCHAIN, "lake"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CORE = [
    "Continuation", "LossBudget", "Rows.Witness", "Rows.Count",
    "Starter.Inverse", "Starter.Nonvanishing", "Energy.Geometry",
    "Energy.WholeIndex", "Energy.CompletedSource", "Energy.PhysicalSource",
    "Principal.Signal", "Principal.Residues", "Moments.Plain",
    "Moments.Exceptional", "Moments.Unconditional", "Moments.Source", "Rows.UniformProfiles",
    "Rows.SourceCount", "SourceData",
]
CORE_ROOTS = [
    "Starter.beta_le_eleven_twelfths", "Rows.from_actual_zero_with_product",
    "Rows.card_bound_from_two_moments", "exists_common_row_then_height_budget",
    "Energy.original_completed_energy_epsilon",
    "Principal.one_prime_principal_comparison",
    "Moments.Unconditional.all_nonprincipal_at", "Moments.finite_plain_bound",
    "Rows.source_plain", "Rows.actual_source_count_uniform_order",
    "beta_le_of_common_deleted_probe",
]
FINAL_ROOTS = ["ZetaZeroFree.Analytic." + n for n in [
    "beta_le_twenty_nine_thirty_thirds", "common_deleted_probe_estimates",
    "heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re",
    "dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re",
    "riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re",
    "Probe.source_data_central_band_bound", "Energy.source_probe_bound",
    "Moments.Unconditional.all_nonprincipal_at",
    "Moments.D3.mixed_plain_moment_radical",
]]

D3_ROOTS = ["ZetaZeroFree.Analytic.Moments.Unconditional.all_nonprincipal_at",
            "ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical"]


def mathematical_modules(root=ROOT):
    audit = root / "ZetaZeroFree/Analytic/Audit.lean"
    return ["ZetaZeroFree.Exponent"] + sorted(
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "ZetaZeroFree/Analytic").rglob("*.lean")
        if path != audit)


def require_unchanged_inventory(modules, root=ROOT):
    if mathematical_modules(root) != modules:
        raise ValueError("Analytic module inventory changed during verification")


def fingerprint(path):
    data = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def run(argv):
    result = subprocess.run(argv, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    return {"argv": argv, "returncode": result.returncode, "output": result.stdout}


def parse_audit(output, modules, roots):
    lines = [line.removeprefix("ANALYTIC_AUDIT ") for line in output.splitlines()
             if line.startswith("ANALYTIC_AUDIT ")]
    if len(lines) != 1:
        raise ValueError("Expected exactly one complete Lean analytic audit")
    report = json.loads(lines[0])
    if set(report["modules"]) != set(modules) or report["required_roots"] != roots:
        raise ValueError("Lean audit module/root binding differs")
    names = [entry["declaration"] for entry in report["axiom_reports"]]
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty or duplicate declaration coverage")
    if len(names) != report["declaration_count"]:
        raise ValueError("Declaration coverage count differs")
    theorems = report["theorems"]
    if (len(theorems) != len(set(theorems)) or len(theorems) != report["theorem_count"]
            or not set(theorems).issubset(names) or not set(roots).issubset(theorems)):
        raise ValueError("Required theorem coverage differs")
    if any(set(entry["axioms"]) - ALLOWED for entry in report["axiom_reports"]):
        raise ValueError("Forbidden analytic axiom")
    if report["forbidden_terminal_dependencies"] or report["missing_declarations"]:
        raise ValueError("Old terminal proof or missing dependency")
    if report["all_reachable_constants"] < len(names):
        raise ValueError("Incomplete dependency walk")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", action="store_true",
                        help="Audit frozen components; does not establish the final endpoint")
    args = parser.parse_args()
    if args.core:
        modules = ["ZetaZeroFree.Analytic." + m for m in CORE]
        roots = ["ZetaZeroFree.Analytic." + n for n in CORE_ROOTS]
        audit_path = ROOT / "evidence/analytic-core-audit.lean"
        report_path = ROOT / "evidence/analytic-core-report.json"
    else:
        final = ROOT / "ZetaZeroFree/Analytic/Final.lean"
        if not final.is_file():
            raise ValueError("The unconditional analytic final module is absent; full acceptance fails")
        modules = mathematical_modules()
        roots = FINAL_ROOTS
        directory = Path(tempfile.mkdtemp(prefix="zeta-analytic-verification-"))
        audit_path, report_path = directory / "audit.lean", directory / "report.json"
    source_paths = [ROOT / (m.replace(".", "/") + ".lean") for m in modules]
    if args.core:
        source_paths.append(ROOT / "ZetaZeroFree/Exponent.lean")
    source_paths += [ROOT / "ZetaZeroFree/Analytic/Audit.lean", Path(__file__).resolve()]
    sources_before = [fingerprint(p) for p in source_paths]
    commands = []
    version = run(PREFIX + ["env", "lean", "--version"])
    commands.append(version)
    if version["returncode"] or "4.34.1" not in version["output"] or COMMIT not in version["output"]:
        raise ValueError("Reference Lean version/commit differs")
    build = run(PREFIX + ["build", "+ZetaZeroFree.Analytic.Audit:olean"] +
                ["+" + m + ":olean" for m in modules])
    commands.append(build)
    if build["returncode"]:
        raise ValueError("Analytic source build failed:\n" + build["output"][-8000:])
    body = "\n".join("import " + m for m in modules)
    body += "\nimport ZetaZeroFree.Analytic.Audit\n\nset_option maxHeartbeats 0\n"
    body += "run_cmd ZetaZeroFree.AnalyticVerification.audit #[" + ", ".join("`" + m for m in modules)
    body += "] #[" + ", ".join("``" + n for n in roots) + "]\n"
    if not args.core:
        body += "run_cmd ZetaZeroFree.AnalyticVerification.auditD3Independence #["
        body += ", ".join("``" + n for n in D3_ROOTS) + "]\n"
    audit_path.write_text(body)
    audit = run(PREFIX + ["env", "lean", "-DautoImplicit=false", str(audit_path)])
    commands.append(audit)
    if audit["returncode"]:
        raise ValueError("Analytic proof-term audit failed:\n" + audit["output"][-8000:])
    proof_audit = parse_audit(audit["output"], modules, roots)
    d3_audit = None
    if not args.core:
        lines = [line.removeprefix("D3_INDEPENDENCE_AUDIT ")
                 for line in audit["output"].splitlines()
                 if line.startswith("D3_INDEPENDENCE_AUDIT ")]
        if len(lines) != 1:
            raise ValueError("Expected exactly one D3 independence audit")
        d3_audit = json.loads(lines[0])
        if (d3_audit["roots"] != D3_ROOTS or d3_audit["forbidden_dependencies"]
                or d3_audit["missing_declarations"] or d3_audit["reachable_constants"] < 2):
            raise ValueError("D3 independence audit failed")
    artifacts = []
    for module in modules + ["ZetaZeroFree.Analytic.Audit"]:
        primary = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        artifacts.append(fingerprint(primary))
        for suffix in (".private", ".server"):
            companion = Path(str(primary) + suffix)
            if companion.is_file():
                artifacts.append(fingerprint(companion))
    if not args.core:
        replay = run(PREFIX + ["env", "leanchecker", "--fresh", "--verbose",
                               "ZetaZeroFree.Analytic.Final"])
        commands.append(replay)
        if replay["returncode"]:
            raise ValueError("Fresh analytic kernel replay failed:\n" + replay["output"][-8000:])
    if not args.core:
        require_unchanged_inventory(modules)
    sources_after = [fingerprint(p) for p in source_paths]
    if sources_after != sources_before:
        raise ValueError("Analytic inputs changed during verification")
    artifacts_after = [fingerprint(ROOT / item["path"]) for item in artifacts]
    if artifacts_after != artifacts:
        raise ValueError("Analytic artifacts changed during verification")
    report = {"schema": "zeta-new-analytic-verification/1", "passed": True,
              "complete_new_endpoint": not args.core,
              "scope": "frozen analytic components" if args.core else "unconditional new 29/33 proof and standalone Appendix D.3",
              "reference": {"toolchain": TOOLCHAIN, "commit": COMMIT},
              "completed_at": datetime.now(timezone.utc).isoformat(),
              "sources": sources_before, "artifacts": artifacts,
              "proof_audit": proof_audit, "d3_independence_audit": d3_audit,
              "commands": commands,
              "audit_source": {"path": str(audit_path),
                               "sha256": hashlib.sha256(audit_path.read_bytes()).hexdigest()}}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"passed": True, "complete_new_endpoint": not args.core,
                      "theorems": proof_audit["theorem_count"],
                      "reachable_constants": proof_audit["all_reachable_constants"],
                      "report": str(report_path)}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
