import { readFileSync, writeFileSync } from "node:fs";
import {
  readJSON,
  sha256,
  authenticate,
  envelope,
  PIN_DIGEST,
} from "./common.mjs";
import { receipt } from "./receipts.mjs";
import { inspectPR } from "./github.mjs";
const policy = readJSON("verifier/trust-policy.json");
// A protected maintainer commissioning record binds the fully tested worker and pins.
const acceptance = readJSON("verifier/acceptance.json");
if (sha256(acceptance) !== policy.acceptance_receipt_sha256)
  throw Error("Worker has not been commissioned");
const a = authenticate(acceptance, policy.publication_keys);
if (
  a.kind !== "qrh-worker-acceptance-v1" ||
  a.worker_image !== policy.worker_image ||
  a.pin_digest !== PIN_DIGEST ||
  a.baseline !== "accepted" ||
  a.adversarial_suite !== "passed" ||
  a.isolation !== "passed"
)
  throw Error("Missing acceptance evidence");
const p = readJSON("out/attempt.json"),
  source = await inspectPR(
    process.env.GITHUB_REPOSITORY,
    Number(process.env.QRH_PR),
  );
if (source.head_sha !== p.source_commit || source.id !== p.manifest.id)
  throw Error("PR changed during verification");
if (p.log_sha256 !== sha256(readFileSync("out/verification.log")))
  throw Error("Log mismatch");
if (p.orchestrator_commit !== process.env.GITHUB_WORKFLOW_SHA)
  throw Error("Artifact came from a different orchestration revision");
const payload = { ...p, kind: "qrh-verification-v1" };
const signed = envelope(
  payload,
  process.env.QRH_SIGNING_KEY,
  process.env.QRH_KEY_ID,
);
receipt(signed, policy);
writeFileSync("out/receipt.json", JSON.stringify(signed, null, 2) + "\n");

const response = await fetch(
  `https://api.github.com/repos/${policy.repository}/check-runs`,
  {
    method: "POST",
    headers: {
      Accept: "application/vnd.github+json",
      "Content-Type": "application/json",
      "X-GitHub-Api-Version": "2022-11-28",
      Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
    },
    body: JSON.stringify({
      name: "qrh/verified-exact-head",
      head_sha: p.source_commit,
      status: "completed",
      conclusion: "success",
      completed_at: p.completed_at,
      external_id: sha256(signed),
      details_url: `https://github.com/${policy.repository}/actions/runs/${process.env.GITHUB_RUN_ID}`,
      output: {
        title: "Comparator and NanoDa accepted this exact source revision",
        summary: `Authenticated receipt SHA-256: ${sha256(signed)}. Content SHA-256: ${p.content_digest}. Publication still requires independent attribution/license review.`,
      },
    }),
  },
);
if (!response.ok)
  throw Error(
    "Could not attach exact-head verification check: " + response.status,
  );
