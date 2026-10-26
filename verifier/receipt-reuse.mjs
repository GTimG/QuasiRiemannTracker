// Run only from the protected workflow checkout, never a candidate checkout.
// Authentication is the maintainer's protected registration plus exact byte hashes,
// not a candidate-written PASS field or a URL supplied by the pull request.
import { lstatSync, readFileSync, readdirSync } from "node:fs";
import { join, dirname } from "node:path";
import { canonical, sha256 } from "./common.mjs";
import { validateAdmission } from "./pr-evidence.mjs";
import { acceptedWorkerReport } from "./worker-report.mjs";
import { challenge, solutionWrapper } from "./challenge.mjs";

const digest = (s) => typeof s === "string" && /^[a-f0-9]{64}$/.test(s);
const require = (condition, message) => {
  if (!condition) throw Error(`Registered receipt: ${message}`);
};
function file(root, path) {
  require(/^[A-Za-z0-9_.\/-]+$/.test(path), "unsafe evidence path");
  const parts = path.split("/");
  require(parts.every(
    (p) => p && p !== "." && p !== "..",
  ), "unsafe evidence path");
  for (let i = 1; i <= parts.length; i++) {
    const stat = lstatSync(join(root, ...parts.slice(0, i)));
    require(!stat.isSymbolicLink(), "symlink evidence is forbidden");
    require(i === parts.length
      ? stat.isFile()
      : stat.isDirectory(), "non-regular evidence");
    require(stat.size <= 32 * 1024 ** 2, "evidence size limit");
  }
  return readFileSync(join(root, path));
}

// Conservative invalidation: changing verifier code, pins, challenge, package
// lock or admission orchestration requires an explicit maintainer re-review.
export function receiptPolicy(root) {
  const paths = [
    "package.json",
    "package-lock.json",
    ".github/workflows/pr-admission.yml",
    ".github/actions/verifier-cache/action.yml",
  ];
  function walk(dir) {
    for (const name of readdirSync(join(root, dir)).sort()) {
      const path = `${dir}/${name}`;
      if (
        name === "__pycache__" ||
        path === "verifier/standard/receipts" ||
        path === "verifier/local-results.json"
      )
        continue;
      const stat = lstatSync(join(root, path));
      require(!stat.isSymbolicLink(), "symlink in verifier policy");
      if (stat.isDirectory()) walk(path);
      else if (/\.(mjs|py|json|lean|pem|patch)$/.test(name)) paths.push(path);
    }
  }
  walk("core");
  walk("verifier");
  return sha256(
    Object.fromEntries(paths.sort().map((p) => [p, sha256(file(root, p))])),
  );
}

export function receiptRuntime(report) {
  return sha256({
    tool_pins: report.tool_pins,
    driver_sha256: report.driver_sha256,
    palomar_sha256: report.palomar_sha256,
    library_inventory_sha256: report.library_inventory_sha256,
  });
}
export function sourceContractDigest(contract) {
  // Fresh source preparation intentionally has no installed library inventory.
  // The approved runtime separately binds the verified library inventory.
  const { library_inventory_sha256, ...source } = contract;
  return sha256(source);
}

export function reusableReceipt(
  root,
  expected,
  { prepared, required = false } = {},
) {
  const registration = validateAdmission(root, expected, {
    optional: !required,
  });
  if (!registration?.reuse) {
    require(!required, "no protected reuse approval for this exact revision");
    return null;
  }
  const approval = registration.reuse;
  require(approval.schema_version === 1 &&
    digest(approval.policy_sha256) &&
    approval.policy_sha256 ===
      receiptPolicy(
        root,
      ), "verifier policy changed; maintainer review required");
  const prefix = `https://github.com/${expected.repository}/blob/`;
  require(registration.report_url.startsWith(
    prefix,
  ), "receipt must belong to this repository");
  const suffix = registration.report_url.slice(prefix.length);
  require(/^[a-f0-9]{40}\/verifier\/standard\/receipts\/[a-z0-9-]+\/result\.json$/.test(
    suffix,
  ), "receipt must have an immutable protected evidence path");
  const path = suffix.slice(41),
    dir = dirname(path);
  const bytes = file(root, path);
  require(sha256(bytes) ===
    registration.report_sha256, "receipt bytes differ from protected registration");
  const report = acceptedWorkerReport(expected, JSON.parse(bytes));
  require(report.source_commit === expected.head_sha &&
    report.verified_at === registration.verified_at &&
    canonical(report.bound_interval ?? null) ===
      canonical(
        registration.bound_interval ?? null,
      ), "certificate differs from accepted proof provenance");
  const toolNames = [
    "source_lean",
    "exporter",
    "judge_lake",
    "judge_lean",
    "judge_leanexport",
    "judge_leanchecker",
    "judge_nanoda_bin",
    "judge_con-ron",
  ];
  require(toolNames.every((k) => digest(report.tool_pins?.[k])) &&
    [
      report.driver_sha256,
      report.palomar_sha256,
      report.library_inventory_sha256,
    ].every(digest) &&
    digest(approval.runtime_sha256) &&
    approval.runtime_sha256 ===
      receiptRuntime(
        report,
      ), "checker, driver or library pins differ from reviewed runtime");
  const contractBytes = file(root, `${dir}/contract.json`);
  require(sha256(contractBytes) ===
    report.artifacts?.["contract.json"], "contract hash mismatch");
  const contract = JSON.parse(contractBytes);
  require(contract.schema_version === 2 &&
    contract.repository === expected.repository &&
    contract.head_sha === expected.head_sha &&
    contract.source_commit === expected.head_sha &&
    contract.manifest?.id === expected.result_id, "contract identity mismatch");
  require((contract.manifest.exact_bound ??
    `${contract.manifest.theta?.numerator}/${contract.manifest.theta?.denominator}`) ===
    expected.theta_exact, "contract bound differs from the registered theorem");
  require(contract.source_files &&
    Object.keys(contract.source_files).length > 0 &&
    canonical(contract.source_files) === canonical(report.source_files) &&
    canonical(contract.submission_trees) ===
      canonical(report.submission_trees) &&
    contract.library_inventory_sha256 ===
      report.library_inventory_sha256, "source or dependency contract mismatch");
  require(canonical(JSON.parse(file(root, `${dir}/dependency-pins.json`))) ===
    canonical(
      JSON.parse(file(root, "verifier/standard/lake-manifest.json")),
    ), "approved library dependency revisions changed");
  require(contract.generated_files?.["Challenge.lean"] ===
    sha256(challenge(contract.manifest)) &&
    contract.generated_files?.["Solution.lean"] ===
      sha256(solutionWrapper(contract.manifest)) &&
    report.artifacts?.["solution-src/Solution.lean"] ===
      contract.generated_files["Solution.lean"] &&
    digest(report.artifacts?.["exports/Challenge.export"]) &&
    digest(
      report.artifacts?.["exports/Solution.export"],
    ), "canonical challenge or export binding mismatch");
  const controlBytes = file(root, `${dir}/controls.json`);
  require(sha256(controlBytes) ===
    report.artifacts?.["controls.json"], "control evidence hash mismatch");
  const controls = JSON.parse(controlBytes);
  require(Array.isArray(controls) &&
    controls.length === 3 &&
    [
      ["accepted", 0],
      ["statement-mismatch", 1],
      ["ill-typed-proof", 1],
    ].every(
      ([name, code]) =>
        controls.filter((c) => c.expected === name && c.exit_code === code)
          .length === 1,
    ), "positive or adversarial controls did not pass");
  if (prepared)
    require(sourceContractDigest(prepared) ===
      sourceContractDigest(
        contract,
      ), "fresh immutable source, dependencies or generated challenge differ from verified contract");
  return { registration, report, contract };
}

// Publisher revalidates protected evidence, not the worker's claimed result.
export function validateRegisteredAttempt(root, expected, attempt, jobResult) {
  require(jobResult ===
    "success", "receipt-validation job did not complete successfully");
  const { registration, contract } = reusableReceipt(root, expected, {
    required: true,
  });
  require(attempt.registration_sha256 === sha256(registration) &&
    attempt.source_contract_sha256 ===
      sourceContractDigest(
        contract,
      ), "worker record differs from protected approval and source contract");
  return registration;
}
