// Load this module from the trusted default-branch checkout.
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { rational, cmp, BASELINE } from "../core/rational.mjs";
import { validateAdmission } from "./pr-evidence.mjs";
import {
  decimalPrecision,
  validateDecimalApproximation,
} from "./pr-decimal.mjs";

export function parseDeclaration(body) {
  const fields = new Map();
  for (const line of (body ?? "").split(/\r?\n/)) {
    if (!line.trim().startsWith("QRH-")) continue;
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
    const match = /^(\d+)\/(\d+)$/.exec(theta_exact);
    if (!match) throw Error("Use an exact reduced fraction");
    const value = rational(match[1], match[2]);
    if (BigInt(value.numerator) <= 0n || cmp(value, BASELINE) > 0)
      throw Error("Bound must be positive and at most 7/8");
  }
  const theta_decimal = fields.get("Decimal");
  decimalPrecision(theta_decimal);
  return { result_id, theta_exact, theta_decimal };
}

export function hasResultSection(body) {
  return (body ?? "").split(/\r?\n/).some((line) => {
    const text = line.trim();
    return (
      /^QRH-(?:Result|Bound|Decimal)\b/i.test(text) ||
      /^#{1,6}\s+(?:new bounds?|QRH[- ]results?)\b/i.test(text)
    );
  });
}

function proofPath(name) {
  return (
    /^(?:proofs|public\/proofs|submissions|catalogue|registry\/records)(?:\/|$)/.test(
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
  return classifyChanges(files);
}

export async function evaluatePR({
  pr,
  files,
  repository,
  defaultBranch,
  root,
  validateEvidence = validateAdmission,
}) {
  const classification = classifyPRChanges({
    pr,
    files,
    repository,
    defaultBranch,
  });
  if (pr.draft) throw Error("Mark the PR ready for review before admission");
  if (classification.maintenance && hasResultSection(pr.body))
    throw Error("Submit QRH results and maintenance changes in separate PRs");
  if (classification.proof && classification.maintenance)
    throw Error(
      "Separate proof changes from maintenance changes, including workflow and verifier changes",
    );
  const declaration = parseDeclaration(pr.body);
  if (!classification.proof)
    return "Maintenance requirements satisfied. Complete website checks and maintainer review before merging.";
  if (!declaration)
    throw Error(
      "Proof, submission or catalogue changes require QRH-Result, QRH-Bound, QRH-Decimal and independently checked evidence",
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
  return `Independent maintainer evidence accepts ${declaration.result_id} at ${declaration.theta_exact} for this exact PR head. Decimal ${declaration.theta_decimal} is accurate and differs from the previous verified bound at this precision.`;
}
