import { readFileSync, writeFileSync } from "node:fs";
import {
  validateCatalogue,
  boundKey,
  verifiedHere,
} from "../core/catalogue.mjs";
import { cmp, decimal } from "../core/rational.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import { certificate } from "../verifier/certificate.mjs";
import { buildSubmissionCatalogue } from "./submission-catalogue.mjs";
const data = validateCatalogue(buildSubmissionCatalogue());
for (const record of catalogueProofRecords(data)) {
  if (record.status !== "framework-verified") continue;
  const name = `certificates/${proofRevision(record)}.json`;
  if (record.certificate_url !== name)
    throw Error(`Missing verification record: ${record.id}`);
  const c = certificate(JSON.parse(readFileSync("public/" + name, "utf8")));
  if (
    c.result_id !== proofRevision(record) ||
    c.theta_exact !== boundKey(record) ||
    c.verified_at !== record.first_verified_at ||
    (record.source_commit && c.source_commit !== record.source_commit) ||
    (record.repository && c.source_repository !== record.repository)
  )
    throw Error(`Verification record differs from catalogue: ${record.id}`);
}
const config = JSON.parse(readFileSync("site.config.json", "utf8"));
const repository = config.repository || process.env.GITHUB_REPOSITORY || null;
if (repository && !/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repository))
  throw Error("Invalid repository");
writeFileSync("public/catalogue.json", JSON.stringify(data, null, 2) + "\n");
writeFileSync(
  "public/site.json",
  JSON.stringify({ ...config, repository }, null, 2) + "\n",
);
// shields.io endpoint for the README's best-bound badge.
const best = data.records
  .filter(verifiedHere)
  .sort((a, b) => cmp(a.theta, b.theta))[0];
writeFileSync(
  "public/bound-badge.json",
  JSON.stringify(
    {
      schemaVersion: 1,
      label: "best verified bound",
      message: best ? `θ ≤ ${decimal(best.theta, 12)}` : "none yet",
      color: "1d5d74",
    },
    null,
    2,
  ) + "\n",
);
console.log(
  `Catalogue: ${data.records.length} results from local submission files.`,
);
