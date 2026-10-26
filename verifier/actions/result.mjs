// These reports are produced by this workflow run, outside candidate mounts.
import { readFileSync, existsSync } from "node:fs";
import { join } from "node:path";
import { acceptedWorkerReport } from "../worker-report.mjs";
import {
  validateRegisteredAttempt,
  reusableReceipt,
} from "../receipt-reuse.mjs";
import { validateAdmission } from "../pr-evidence.mjs";
export const identityKeys = [
  "repository",
  "number",
  "head_sha",
  "result_id",
  "theta_exact",
];
export function verificationResult(
  root,
  expected,
  attempt,
  jobResult = "success",
  fallback = validateAdmission,
) {
  if (!attempt || !identityKeys.every((k) => attempt[k] === expected[k]))
    throw Error(
      "Verification report is missing or belongs to a different PR head, result ID or bound",
    );
  if (attempt.status === "registered")
    return validateRegisteredAttempt(root, expected, attempt, jobResult);
  if (
    ["infrastructure-blocked", "resource-exhausted"].includes(attempt.status)
  ) {
    try {
      const record = fallback(root, expected);
      // A reuse approval must not bypass its policy check through the legacy
      // resource-failure route when preparation could not run.
      return record?.reuse
        ? reusableReceipt(root, expected, { required: true }).registration
        : record;
    } catch {
      throw Error(
        `${attempt.reason}. Retry verification on a suitable worker, or register a matching independently verified local run.`,
      );
    }
  }
  if (attempt.status !== "accepted")
    throw Error(attempt.reason || "Proof verification did not complete");
  if (jobResult !== "success")
    throw Error("Verification job did not complete successfully");
  return acceptedWorkerReport(expected, attempt.report);
}

export function currentVerification(root, expected) {
  const filename = join(root, "verification/attempt.json");
  if (!existsSync(filename))
    throw Error("Proof verification has not run for this PR head");
  return verificationResult(
    root,
    expected,
    JSON.parse(readFileSync(filename, "utf8")),
    process.env.QRH_VERIFICATION_RESULT,
  );
}
