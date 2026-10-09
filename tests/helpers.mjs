import { generateKeyPairSync } from "node:crypto";
import { readFileSync } from "node:fs";
import { envelope, readJSON, sha256, PIN_DIGEST } from "../verifier/common.mjs";
import { challenge } from "../verifier/challenge.mjs";
export function setup() {
  const vk = generateKeyPairSync("ed25519"),
    pk = generateKeyPairSync("ed25519");
  const policy = {
    repository: "owner/qrh",
    maintainers: ["reviewer"],
    verification_keys: { v: vk.publicKey },
    publication_keys: { p: pk.publicKey },
    worker_image: "sha256:" + "a".repeat(64),
    accepted_pin_digests: [PIN_DIGEST],
  };
  const m = readJSON("submissions/openai-baseline/manifest.json"),
    log = "Comparator and NanoDa log fixture for TESTS ONLY\n";
  const payload = {
    kind: "qrh-verification-v1",
    status: "accepted",
    results: {
      comparator: "accepted",
      nanoda: "accepted",
      isolation: "passed",
    },
    source_commit: "b".repeat(40),
    orchestrator_commit: "c".repeat(40),
    content_digest: "d".repeat(64),
    log_sha256: sha256(log),
    manifest: m,
    manifest_digest: sha256(m),
    challenge_sha256: sha256(challenge(m)),
    repository: policy.repository,
    pr: 1,
    pin_digest: PIN_DIGEST,
    worker_image: policy.worker_image,
    verified_at: "2026-10-01T12:00:00.000Z",
  };
  const receipt = envelope(payload, vk.privateKey, "v");
  const publicationPayload = {
    kind: "qrh-publication-v1",
    id: m.id,
    repository: policy.repository,
    pr: 1,
    pr_author: "author",
    source_commit: payload.source_commit,
    content_digest: payload.content_digest,
    receipt_sha256: sha256(receipt),
    reviews: [{ login: "reviewer", commit_id: payload.source_commit }],
    submitted_at: "2026-10-01T10:00:00.000Z",
    merged_at: "2026-10-01T13:00:00.000Z",
    published_at: "2026-10-01T14:00:00.000Z",
  };
  return {
    policy,
    payload,
    receipt,
    publicationPayload,
    log,
    vk,
    pk,
    bundle: {
      receipt,
      publication: envelope(publicationPayload, pk.privateKey, "p"),
      log,
    },
  };
}
