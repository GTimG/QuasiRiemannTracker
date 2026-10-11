// Load this module, pins, admissions and evidence from the trusted base checkout.
import { lstatSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { validateMaintainerReplay } from "../core/maintainer-replay.mjs";

const demand = (ok, message) => {
  if (!ok) throw Error(`PR admission: ${message}`);
};
const object = (value) =>
  value !== null && typeof value === "object" && !Array.isArray(value);
const identityKeys = [
  "repository",
  "number",
  "head_sha",
  "result_id",
  "theta_exact",
];
function identity(value) {
  demand(
    object(value) &&
      typeof value.repository === "string" &&
      /^[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+$/.test(value.repository) &&
      ![".", ".."].includes(value.repository.split("/")[1]) &&
      Number.isSafeInteger(value.number) &&
      value.number > 0 &&
      typeof value.head_sha === "string" &&
      /^[a-f0-9]{40}$/.test(value.head_sha) &&
      typeof value.result_id === "string" &&
      /^[a-z][a-z0-9-]{2,63}$/.test(value.result_id) &&
      typeof value.theta_exact === "string" &&
      value.theta_exact.length > 0 &&
      value.theta_exact.length <= 256 &&
      value.theta_exact === value.theta_exact.trim() &&
      !/[\x00-\x1f\x7f]/.test(value.theta_exact),
    "invalid admission identity",
  );
}

export function validateAdmission(root, expected) {
  identity(expected);
  const file = join(root, "verifier/pr-admissions.json");
  const stat = lstatSync(file);
  demand(stat.isFile() && !stat.isSymbolicLink(), "unsafe admissions file");
  const policy = JSON.parse(readFileSync(file, "utf8"));
  demand(
    object(policy) &&
      policy.schema_version === 1 &&
      Array.isArray(policy.admissions) &&
      Object.keys(policy).sort().join(",") === "admissions,schema_version",
    "invalid admissions policy",
  );
  const seen = new Set();
  const matches = [];
  for (const entry of policy.admissions) {
    identity(entry);
    demand(
      Object.keys(entry).sort().join(",") ===
        [...identityKeys, "pin", "contribution"].sort().join(",") &&
        object(entry.pin) &&
        object(entry.contribution),
      "invalid admission entry",
    );
    // A single contribution at an exact PR head has one approved bound.
    // Require a unique approval for each identity.
    const key = JSON.stringify([
      entry.repository.toLowerCase(),
      entry.number,
      entry.head_sha,
      entry.result_id,
    ]);
    demand(!seen.has(key), "duplicate admission identity");
    seen.add(key);
    if (identityKeys.every((key) => entry[key] === expected[key]))
      matches.push(entry);
  }
  demand(
    matches.length === 1,
    "archive an independent maintainer replay on the base branch for this exact PR head, result ID and bound",
  );
  const entry = matches[0];
  const report = validateMaintainerReplay(root, entry.pin, entry.contribution);
  demand(
    report.reviewed_pr_head === expected.head_sha,
    "receipt must verify this exact PR head",
  );
  demand(
    report.theta_exact === expected.theta_exact,
    "receipt must verify the declared exact bound",
  );
  return report;
}
