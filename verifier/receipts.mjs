import { authenticate, sha256, PIN_DIGEST } from "./common.mjs";
import { manifest } from "./manifest.mjs";
import { challenge } from "./challenge.mjs";
const hex = /^[a-f0-9]{64}$/,
  commit = /^[a-f0-9]{40}$/;
export function receipt(record, policy, expected) {
  const p = authenticate(record, policy.verification_keys);
  if (
    p.kind !== "qrh-verification-v1" ||
    p.status !== "accepted" ||
    p.results?.comparator !== "accepted" ||
    p.results?.nanoda !== "accepted" ||
    p.results?.isolation !== "passed"
  )
    throw Error("Not a successful verification");
  if (
    p.pin_digest !== PIN_DIGEST ||
    !policy.accepted_pin_digests.includes(p.pin_digest)
  )
    throw Error("Unapproved verifier pins");
  if (
    !commit.test(p.source_commit) ||
    !commit.test(p.orchestrator_commit) ||
    !hex.test(p.content_digest) ||
    !hex.test(p.log_sha256) ||
    p.worker_image !== policy.worker_image ||
    !/^sha256:[a-f0-9]{64}$/.test(p.worker_image)
  )
    throw Error("Invalid provenance");
  if (
    p.repository !== policy.repository ||
    !Number.isSafeInteger(p.pr) ||
    p.pr < 1
  )
    throw Error("Wrong repository or PR");
  manifest(p.manifest);
  if (
    p.manifest_digest !== sha256(p.manifest) ||
    p.challenge_sha256 !== sha256(challenge(p.manifest))
  )
    throw Error("Statement binding mismatch");
  if (
    !/^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d{3}Z$/.test(p.verified_at) ||
    !Number.isFinite(Date.parse(p.verified_at))
  )
    throw Error("Invalid verification date");
  if (expected) {
    for (const k of [
      "source_commit",
      "content_digest",
      "manifest_digest",
      "repository",
      "pr",
    ])
      if (p[k] !== expected[k])
        throw Error("Stale or mismatched receipt: " + k);
  }
  return p;
}
export function reviewed(pr, reviews, policy) {
  if (
    pr.base_repository !== policy.repository ||
    pr.is_draft ||
    !pr.merged_at ||
    !pr.merge_commit ||
    !commit.test(pr.head_sha)
  )
    throw Error("Publication requires a merged, reviewed PR");
  // Latest review per person wins; a later dismissal/change request revokes approval.
  const latest = new Map();
  for (const r of [...reviews].sort((a, b) =>
    a.submitted_at.localeCompare(b.submitted_at),
  ))
    latest.set(r.login, r);
  const approvals = [...latest.values()].filter(
    (r) =>
      r.state === "APPROVED" &&
      r.commit_id === pr.head_sha &&
      r.login !== pr.author &&
      policy.maintainers.includes(r.login),
  );
  if (!approvals.length)
    throw Error(
      "Independent maintainer attribution/license review of this exact head required",
    );
  return approvals.map((r) => ({
    login: r.login,
    commit_id: r.commit_id,
    review_id: r.id,
    submitted_at: r.submitted_at,
  }));
}
export function publication(record, policy) {
  const p = authenticate(record, policy.publication_keys);
  if (p.kind !== "qrh-publication-v1" || p.repository !== policy.repository)
    throw Error("Invalid publication");
  if (
    !Array.isArray(p.reviews) ||
    !p.reviews.some(
      (r) =>
        r.login !== p.pr_author &&
        policy.maintainers.includes(r.login) &&
        r.commit_id === p.source_commit,
    )
  )
    throw Error("Publication lacks independent exact-head review");
  for (const k of ["submitted_at", "published_at", "merged_at"])
    if (!Number.isFinite(Date.parse(p[k])))
      throw Error("Invalid publication dates");
  if (!hex.test(p.receipt_sha256)) throw Error("Invalid receipt binding");
  return p;
}
export function event(record, policy) {
  const e = authenticate(record, policy.publication_keys);
  if (
    e.kind !== "qrh-event-v1" ||
    !["withdraw", "supersede"].includes(e.type) ||
    typeof e.reason !== "string" ||
    !e.reason ||
    !Number.isFinite(Date.parse(e.at)) ||
    !policy.maintainers.includes(e.reviewer)
  )
    throw Error("Invalid history event");
  if (e.type === "supersede" && (!e.replacement || e.replacement === e.id))
    throw Error("Supersession requires another contribution");
  return e;
}
