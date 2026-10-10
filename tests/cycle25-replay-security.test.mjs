import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
test("Cycle25 source ingestion rejects stale bytes, unsafe archives and host-path leaks", () => {
  const result = spawnSync("python3", ["tests/cycle25_replay_security.py"], {
    encoding: "utf8",
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
});
