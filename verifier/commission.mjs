import { readFileSync, readdirSync, writeFileSync } from "node:fs";
import {
  readJSON,
  PIN_DIGEST,
  sha256,
  envelope,
  authenticate,
} from "./common.mjs";
// Run only during maintainer commissioning, OUTSIDE the candidate environment.
const policy = readJSON("verifier/trust-policy.json"),
  summary = readJSON("evidence/integration/summary.json");
const expected = ["baseline", ...readdirSync("tests/adversarial").sort()];
if (
  summary.baseline !== "accepted" ||
  summary.adversarial_suite !== "passed" ||
  summary.isolation !== "passed" ||
  summary.pin_digest !== PIN_DIGEST ||
  summary.worker_image !== policy.worker_image
)
  throw Error("Baseline, adversarial or isolation acceptance is missing");
if (
  JSON.stringify(summary.results.map((r) => r.id).sort()) !==
  JSON.stringify(expected.sort())
)
  throw Error("Incomplete integration suite");
for (const r of summary.results) {
  if (sha256(readFileSync(`evidence/integration/${r.id}.log`)) !== r.log_sha256)
    throw Error("Acceptance log mismatch");
}
const payload = {
  ...summary,
  kind: "qrh-worker-acceptance-v1",
  summary_sha256: sha256(summary),
};
const signed = envelope(
  payload,
  process.env.QRH_PUBLICATION_KEY,
  process.env.QRH_PUBLICATION_KEY_ID,
);
authenticate(signed, policy.publication_keys);
writeFileSync(
  "verifier/acceptance.json",
  JSON.stringify(signed, null, 2) + "\n",
  { flag: "wx" },
);
console.log(
  "Review and pin this acceptance_receipt_sha256 in a separate infrastructure PR:",
  sha256(signed),
);
