// Local results are read from the protected base checkout. Candidate files cannot register one.
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { certificate } from "./certificate.mjs";
export function validateAdmission(root, expected, { optional = false } = {}) {
  const entries = JSON.parse(
    readFileSync(join(root, "verifier/local-results.json"), "utf8"),
  );
  const keys = ["repository", "number", "head_sha", "result_id", "theta_exact"];
  const matches = entries.filter((entry) =>
    keys.every((key) => entry[key] === expected[key]),
  );
  if (optional && matches.length === 0) return null;
  if (matches.length !== 1)
    throw Error(
      "A verified local run must match this exact PR head, result ID and bound",
    );
  const entry = matches[0];
  certificate(entry);
  if (
    entry.source_commit !== expected.head_sha ||
    entry.source_repository !== expected.repository
  )
    throw Error("Local verification source differs from this PR head");
  return entry;
}
