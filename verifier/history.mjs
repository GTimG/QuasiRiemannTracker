import { receipt } from "./receipts.mjs";
import { sha256 } from "./common.mjs";
// Journal files are content-addressed and protected as append-only infrastructure.
export function firstSuccess(history, policy, current) {
  const valid = history
    .map((r) => ({ envelope: r, payload: receipt(r, policy) }))
    .filter(
      (r) =>
        r.payload.manifest.id === current.manifest.id &&
        r.payload.content_digest === current.content_digest &&
        r.payload.source_commit === current.source_commit,
    )
    .sort(
      (a, b) =>
        a.payload.verified_at.localeCompare(b.payload.verified_at) ||
        sha256(a.envelope).localeCompare(sha256(b.envelope)),
    );
  if (!valid.length)
    throw Error(
      "Verification must be archived in the protected journal before publication",
    );
  return valid[0];
}
export function immutableHistory(before, after) {
  for (const [file, digest] of Object.entries(before))
    if (after[file] !== digest)
      throw Error("Historical records cannot be edited or removed: " + file);
}
