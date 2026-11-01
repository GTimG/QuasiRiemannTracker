import { test } from "node:test";
import assert from "node:assert/strict";
import { contributorLeaderboard } from "../core/contributors.mjs";
const record = (id, day, numerator, denominator, names) => ({
  id,
  timeline_at: `2026-01-0${day}T00:00:00Z`,
  theta: { numerator: String(numerator), denominator: String(denominator) },
  authors: names.map((name) => ({ name })),
});
test("aggregates exact signed deltas per person, ranks totals and retains each best bound", () => {
  const records = [
    record("base", 1, 1, 1, ["Baseline"]),
    record("a", 2, 3, 4, ["Alice"]),
    record("b", 3, 7, 10, ["Bob"]),
    record("c", 4, 3, 5, ["Alice", "Carol"]),
    record("d", 5, 4, 5, ["Bob"]),
  ];
  const result = contributorLeaderboard(records.reverse());
  assert.deepEqual(
    result.map((p) => p.name),
    ["Alice", "Carol", "Baseline", "Bob"],
  );
  assert.deepEqual(result[0].improvement, {
    numerator: "7",
    denominator: "20",
  });
  assert.equal(result[0].best.id, "c");
  assert.equal(result[0].count, 2);
  assert.deepEqual(result.at(-1).improvement, {
    numerator: "-3",
    denominator: "20",
  });
  assert.equal(result.at(-1).best.id, "b");
});
test("normalizes names and credits a repeated coauthor only once per submission", () => {
  const result = contributorLeaderboard([
    record("base", 1, 1, 1, ["A"]),
    record("next", 2, 1, 2, [" A ", "a"]),
  ]);
  assert.equal(result.length, 1);
  assert.equal(result[0].count, 2);
  assert.deepEqual(result[0].improvement, { numerator: "1", denominator: "2" });
});
test("empty catalogue has no contributors", () =>
  assert.deepEqual(contributorLeaderboard([]), []));
