import { cpSync, mkdirSync, writeFileSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { sha256 } from "../../verifier/common.mjs";
import { challenge, solutionWrapper } from "../../verifier/challenge.mjs";
import {
  receiptPolicy,
  receiptRuntime,
  sourceContractDigest,
} from "../../verifier/receipt-reuse.mjs";

// Synthetic security fixture, never a published proof or verification receipt.
export function registeredFixture(
  root,
  expected = {
    repository: "GTimG/QuasiRiemannTracker",
    number: 15,
    head_sha: "a".repeat(40),
    result_id: "candidate-proof",
    theta_exact: "1/1",
  },
) {
  const project = fileURLToPath(new URL("../../", import.meta.url));
  for (const path of [
    "core",
    "verifier",
    ".github",
    "package.json",
    "package-lock.json",
  ])
    cpSync(join(project, path), join(root, path), {
      recursive: true,
      filter: (p) =>
        !p.includes("/receipts") &&
        !p.includes("/__pycache__") &&
        !p.endsWith("/local-results.json"),
    });
  const dir = "verifier/standard/receipts/test-receipt";
  mkdirSync(join(root, dir), { recursive: true });
  const manifest = {
    id: expected.result_id,
    theta: { numerator: "1", denominator: "1" },
    entrypoint: { module: "Candidate.Main", declaration: "Candidate.bound" },
  };
  const contract = {
    schema_version: 2,
    repository: expected.repository,
    head_sha: expected.head_sha,
    source_commit: expected.head_sha,
    manifest,
    source_files: {
      "metadata.json": sha256("metadata"),
      "src/Candidate/Main.lean": sha256("proof"),
    },
    submission_trees: { [expected.result_id]: "e".repeat(40) },
    module_dependencies: { "Candidate.Main": [] },
    package_imports: [],
    build_order: ["Candidate.Main"],
    generated_files: {
      "Challenge.lean": sha256(challenge(manifest)),
      "Solution.lean": sha256(solutionWrapper(manifest)),
    },
    library_inventory_sha256: sha256("reviewed private libraries"),
  };
  const controls = [
    { expected: "accepted", exit_code: 0 },
    { expected: "statement-mismatch", exit_code: 1 },
    { expected: "ill-typed-proof", exit_code: 1 },
  ];
  const report = {
    status: "PASS",
    verified_at: "2026-10-13T00:00:00Z",
    reviewed_pr_head: expected.head_sha,
    source_commit: expected.head_sha,
    source_repository: expected.repository,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    targets: ["QRH.canonical_bound"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
    kernels: ["Lean default", "nanoda", "con-ron"],
    judge_exit_code: 0,
    sandbox_preflight: "PASS",
    candidate_mount_preflight: "PASS",
    challenge_exported_before_candidate_execution: true,
    receipt_outside_candidate: true,
    source_files: contract.source_files,
    submission_trees: contract.submission_trees,
    library_inventory_sha256: contract.library_inventory_sha256,
    driver_sha256: sha256("driver"),
    palomar_sha256: sha256("sandbox"),
    tool_pins: Object.fromEntries(
      [
        "source_lean",
        "exporter",
        "judge_lake",
        "judge_lean",
        "judge_leanexport",
        "judge_leanchecker",
        "judge_nanoda_bin",
        "judge_con-ron",
      ].map((k) => [k, sha256(k)]),
    ),
    artifacts: {
      "solution-src/Solution.lean": contract.generated_files["Solution.lean"],
      "exports/Challenge.export": sha256("challenge export"),
      "exports/Solution.export": sha256("proof export"),
    },
  };
  const registration = {
    schema_version: 1,
    ...expected,
    source_repository: expected.repository,
    source_commit: expected.head_sha,
    verified_at: report.verified_at,
    kernels: report.kernels,
    report_url: `https://github.com/${expected.repository}/blob/${"b".repeat(40)}/${dir}/result.json`,
    reuse: {
      schema_version: 1,
      policy_sha256: receiptPolicy(root),
      runtime_sha256: receiptRuntime(report),
    },
  };
  const write = (path, value) =>
    writeFileSync(join(root, path), JSON.stringify(value, null, 2) + "\n");
  function seal() {
    write(`${dir}/contract.json`, contract);
    write(`${dir}/controls.json`, controls);
    report.artifacts["contract.json"] = sha256(
      readFileSync(join(root, dir, "contract.json")),
    );
    report.artifacts["controls.json"] = sha256(
      readFileSync(join(root, dir, "controls.json")),
    );
    write(`${dir}/result.json`, report);
    registration.report_sha256 = sha256(
      readFileSync(join(root, dir, "result.json")),
    );
    write("verifier/local-results.json", [registration]);
  }
  cpSync(
    join(root, "verifier/standard/lake-manifest.json"),
    join(root, dir, "dependency-pins.json"),
  );
  seal();
  const attempt = () => ({
    ...expected,
    status: "registered",
    registration_sha256: sha256(registration),
    source_contract_sha256: sourceContractDigest(contract),
  });
  return {
    expected,
    dir,
    contract,
    controls,
    report,
    registration,
    seal,
    write,
    attempt,
  };
}
