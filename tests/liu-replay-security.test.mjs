import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";

test("Liu replay ingests source as inert data and rejects changed hashes and unsafe archives", () => {
  const result = spawnSync("python3", ["tests/liu_replay_security.py"], {
    encoding: "utf8",
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
});

test("current Liu instructions route to the reviewed sandbox and label the archived native route", async () => {
  const { readFileSync } = await import("node:fs");
  const data = JSON.parse(readFileSync("catalogue/results.json", "utf8"));
  const record = data.records.find((item) => item.id === "liu-20261008");
  const reference = record.references.find(
    (item) => item.label === "Sandboxed reproduction instructions",
  );
  assert.equal(
    readFileSync(`public/${reference.url}`, "utf8"),
    readFileSync("verifier/liu/README.md", "utf8"),
  );
  const historical = record.references.find(
    (item) => item.url === "proofs/liu-20261010-kernels/README.txt",
  );
  assert.match(historical.label, /Historical.*unsafe/);
});
