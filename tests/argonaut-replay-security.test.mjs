import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";

test("Argonaut ingestion authenticates the nested release without running author scripts", () => {
  const result = spawnSync("python3", ["tests/argonaut_replay_security.py"], {
    encoding: "utf8",
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
});

test("Argonaut's displayed verification requires the fresh sandboxed replay", () => {
  const catalogue = JSON.parse(readFileSync("catalogue/results.json", "utf8"));
  const record = catalogue.records.find((r) => r.id === "argonaut-20261008");
  const pins = JSON.parse(
    readFileSync("core/external-kernel-pins/argonaut-20261008.json", "utf8"),
  );
  assert.equal(pins.maintainer_replay.replay_profile, "argonaut-v0.1.8");
  const receipt = JSON.parse(
    readFileSync(`${pins.maintainer_replay.directory}/result.json`, "utf8"),
  );
  assert.equal(
    record.first_verified_at,
    pins.maintainer_replay.first_acceptance?.verified_at ?? receipt.verified_at,
  );
  const guide = record.references.find(
    (r) => r.label === "Sandboxed reproduction instructions",
  );
  assert.equal(
    readFileSync(`public/${guide.url}`, "utf8"),
    readFileSync("verifier/argonaut/README.md", "utf8"),
  );
  const historical = record.references.find(
    (r) => r.url === "proofs/argonaut-20261010-kernels/README.txt",
  );
  assert.match(historical.label, /Historical.*unsafe/);
});
