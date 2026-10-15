// Load this module from the trusted default-branch checkout.
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { rational } from "../core/rational.mjs";
import { maintenanceVerification } from "./pr-maintenance.mjs";
import { currentVerification } from "./actions/result.mjs";
import {
  decimalPrecision,
  validateDecimalApproximation,
} from "./pr-decimal.mjs";

export function parseDeclaration(body) {
  const fields = new Map();
  for (const line of (body ?? "").split(/\r?\n/)) {
    if (!/^QRH-/i.test(line.trim())) continue;
    const match = /^QRH-(Result|Bound|Decimal): ([^\r\n]+)$/.exec(line.trim());
    if (!match) throw Error("Malformed or unknown QRH declaration field");
    if (fields.has(match[1])) throw Error("Duplicate QRH declaration field");
    fields.set(match[1], match[2].trim());
  }
  if (!fields.size) return null;
  const result_id = fields.get("Result"),
    theta_exact = fields.get("Bound");
  if (!/^[a-z][a-z0-9-]{2,63}$/.test(result_id ?? ""))
    throw Error("New bounds require QRH-Result: <stable-result-id>");
  if (
    !theta_exact ||
    theta_exact.length > 256 ||
    /[\x00-\x1f\x7f]/.test(theta_exact)
  )
    throw Error("New bounds require QRH-Bound: <exact checked value>");
  // Rational literals must be canonical. Algebraic expressions are compared
  // byte-for-byte with the trusted replay's exact bound.
  if (/^[\d\s+./-]+$/.test(theta_exact)) {
    const match = /^(-?\d+)\/(\d+)$/.exec(theta_exact);
    if (!match) throw Error("Use an exact reduced fraction");
    const value = rational(match[1], match[2]);
    if (BigInt(value.numerator) <= 0n) throw Error("Bound must be positive");
  }
  const theta_decimal = fields.get("Decimal");
  decimalPrecision(theta_decimal);
  return { result_id, theta_exact, theta_decimal };
}

export function hasResultSection(body) {
  return (body ?? "")
    .split(/\r?\n/)
    .some((line) => /^QRH-(?:Result|Bound|Decimal)\b/i.test(line.trim()));
}

function proofPath(name) {
  return (
    /^(?:proofs|public\/proofs|public\/certificates|submissions|catalogue|registry\/records)(?:\/|$)/.test(
      name,
    ) ||
    ["public/catalogue.json", "public/registry.json"].includes(name) ||
    (/\.lean$/i.test(name) && !/^(?:verifier|core|tests)\//.test(name))
  );
}

function paths(files) {
  return files.flatMap((file) => {
    if (typeof file.filename !== "string" || !file.filename)
      throw Error("Invalid changed-file response");
    if (file.status === "renamed" && !file.previous_filename)
      throw Error("Renamed file is missing its previous path");
    return [
      file.filename,
      ...(file.previous_filename ? [file.previous_filename] : []),
    ];
  });
}

export function classifyChanges(files) {
  const changedPaths = paths(files);
  return {
    proof: changedPaths.some(proofPath),
    maintenance: changedPaths.some((name) => !proofPath(name)),
  };
}

export function classifyPRChanges({ pr, files, repository, defaultBranch }) {
  if (pr.base?.repo?.full_name !== repository || pr.base?.ref !== defaultBranch)
    throw Error(
      "Admission requires a PR targeting this repository's default branch",
    );
  if (
    !Number.isSafeInteger(pr.number) ||
    pr.number < 1 ||
    !/^[a-f0-9]{40}$/.test(pr.head?.sha ?? "")
  )
    throw Error("Invalid PR identity or head commit");
  if (pr.state !== "open") throw Error("Admission requires an open PR");
  if (
    !Array.isArray(files) ||
    !files.length ||
    files.length !== pr.changed_files ||
    new Set(files.map((f) => f.filename)).size !== files.length
  )
    throw Error(
      "Incomplete or duplicate PR file list; refusing a truncated diff",
    );
  const classification = classifyChanges(files);
  return hasResultSection(pr.body)
    ? classification
    : { proof: false, maintenance: true };
}

export async function evaluatePR({
  pr,
  files,
  repository,
  defaultBranch,
  root,
  validateEvidence = currentVerification,
  validateMaintenance = maintenanceVerification,
  validateProofs,
}) {
  const classification = classifyPRChanges({
    pr,
    files,
    repository,
    defaultBranch,
  });
  if (classification.maintenance && hasResultSection(pr.body))
    throw Error("Submit QRH results and maintenance changes in separate PRs");
  const declaration = parseDeclaration(pr.body);
  if (!declaration) {
    const plan = await validateMaintenance(root, { pr, files, repository });
    const expected = plan.map((item) => ({
      repository,
      number: pr.number,
      head_sha: pr.head.sha,
      ...item,
    }));
    if (expected.length) {
      if (validateProofs) await validateProofs(root, expected);
      else for (const item of expected) await validateEvidence(root, item);
    }
    return `Maintenance requirements satisfied. Validated affected catalogue data and ${expected.length} proof(s).`;
  }
  const prefix = `submissions/${declaration.result_id}/`;
  if (paths(files).some((path) => !path.startsWith(prefix)))
    throw Error(
      `A QRH result PR changes only ${prefix}; edit existing submissions in a maintenance PR`,
    );
  const evidence = await validateEvidence(root, {
    repository,
    number: pr.number,
    head_sha: pr.head.sha,
    result_id: declaration.result_id,
    theta_exact: declaration.theta_exact,
  });
  validateDecimalApproximation({
    theta_exact: declaration.theta_exact,
    theta_decimal: declaration.theta_decimal,
    bound_interval: evidence?.bound_interval,
    catalogue: JSON.parse(
      readFileSync(join(root, "catalogue/results.json"), "utf8"),
    ),
  });
  return `Proof verification accepts ${declaration.result_id} at ${declaration.theta_exact} for this exact PR head. Decimal ${declaration.theta_decimal} accurately approximates the exact bound.`;
}
