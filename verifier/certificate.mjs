import { sha256 } from "./common.mjs";
import { boundLabel } from "../core/catalogue.mjs";
import { proofRevision } from "../core/catalogue-revisions.mjs";
export const KERNELS = ["Lean default", "nanoda", "con-ron"];
export function certificate(value) {
  if (
    value?.schema_version !== 1 ||
    !/^[a-z][a-z0-9-]{2,63}$/.test(value.result_id ?? "") ||
    typeof value.theta_exact !== "string" ||
    !value.theta_exact.trim() ||
    value.theta_exact.length > 256 ||
    !Number.isFinite(Date.parse(value.verified_at)) ||
    !/^[\w.-]+\/[\w.-]+$/.test(value.source_repository ?? "") ||
    !/^[a-f0-9]{40}$/.test(value.source_commit ?? "") ||
    !/^[a-f0-9]{64}$/.test(value.report_sha256 ?? "") ||
    !/^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(?:blob\/[a-f0-9]{40}\/[^\s]+|actions\/runs\/[0-9]+(?:\/attempts\/[0-9]+)?)$/.test(
      value.report_url ?? "",
    ) ||
    JSON.stringify(value.kernels) !== JSON.stringify(KERNELS)
  )
    throw Error("Invalid verification record");
  return value;
}
// Historical verification provenance lives with the corresponding Lean source.
export function historicalCertificate(metadata) {
  return certificate({
    schema_version: 1,
    result_id: proofRevision(metadata),
    theta_exact: boundLabel(metadata),
    verified_at: metadata.first_verified_at,
    source_repository:
      metadata.repository || metadata.verification?.source_repository,
    source_commit:
      metadata.source_commit || metadata.verification?.source_commit,
    kernels: KERNELS,
    report_url: metadata.verification?.report_url,
    report_sha256: metadata.verification?.report_sha256,
    ...(metadata.bound_interval
      ? { bound_interval: metadata.bound_interval }
      : {}),
  });
}
// Call after verificationResult has authenticated a successful worker report.
export function workerCertificate(expected, report, reportUrl, reportBytes) {
  if (sha256(JSON.parse(reportBytes)) !== sha256(report))
    throw Error("Archived report differs from the accepted worker report");
  return certificate({
    schema_version: 1,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    verified_at: report.verified_at,
    source_repository: expected.repository,
    source_commit: expected.head_sha,
    kernels: KERNELS,
    report_url: reportUrl,
    report_sha256: sha256(reportBytes),
    ...(report.bound_interval ? { bound_interval: report.bound_interval } : {}),
  });
}
