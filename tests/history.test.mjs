import test from "node:test";
import assert from "node:assert/strict";
import { firstSuccess, immutableHistory } from "../verifier/history.mjs";
import { setup } from "./helpers.mjs";
import { envelope, sha256 } from "../verifier/common.mjs";
import { generateRegistry } from "../verifier/registry.mjs";
test("publication uses first authenticated success for the exact revision, not a later rerun", () => {
  const t = setup(),
    later = envelope(
      { ...t.payload, verified_at: "2026-10-01T12:30:00.000Z" },
      t.vk.privateKey,
      "v",
    );
  assert.equal(
    firstSuccess([later, t.receipt], t.policy, t.payload).payload.verified_at,
    t.payload.verified_at,
  );
  assert.throws(() => firstSuccess([], t.policy, t.payload));
  const publication = envelope(
    { ...t.publicationPayload, receipt_sha256: sha256(later) },
    t.pk.privateKey,
    "p",
  );
  assert.throws(() =>
    generateRegistry(
      [{ ...t.bundle, receipt: later, publication }],
      [],
      t.policy,
      [t.receipt, later],
    ),
  );
});
test("immutable journal permits appends, refuses altered or deleted evidence", () => {
  assert.doesNotThrow(() =>
    immutableHistory(
      { "records/a": "abc" },
      { "records/a": "abc", "records/b": "def" },
    ),
  );
  assert.throws(() => immutableHistory({ "records/a": "abc" }, {}));
  assert.throws(() =>
    immutableHistory({ "records/a": "abc" }, { "records/a": "def" }),
  );
});
