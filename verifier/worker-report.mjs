// Shared acceptance contract for fresh workers and authenticated registered receipts.
export function acceptedWorkerReport(expected, r) {
  if (
    r?.status !== "PASS" ||
    r.reviewed_pr_head !== expected.head_sha ||
    r.source_repository !== expected.repository ||
    r.result_id !== expected.result_id ||
    r.theta_exact !== expected.theta_exact ||
    r.judge_exit_code !== 0 ||
    JSON.stringify(r.targets) !== JSON.stringify(["QRH.canonical_bound"]) ||
    JSON.stringify(r.kernels) !==
      JSON.stringify(["Lean default", "nanoda", "con-ron"]) ||
    JSON.stringify([...(r.allowed_axioms ?? [])].sort()) !==
      JSON.stringify(["Classical.choice", "Quot.sound", "propext"]) ||
    r.sandbox_preflight !== "PASS" ||
    r.candidate_mount_preflight !== "PASS" ||
    r.challenge_exported_before_candidate_execution !== true ||
    r.receipt_outside_candidate !== true
  )
    throw Error(
      "Verification report does not establish the canonical bound with all three kernels",
    );
  return r;
}
