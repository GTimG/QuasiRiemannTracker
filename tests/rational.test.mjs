import test from "node:test";
import assert from "node:assert/strict";
import {
  rational,
  cmp,
  sub,
  BASELINE,
  recordHistory,
  activeRecords,
  frontierHistory,
  relativePosition,
  decimal,
  scientific,
  log10Rational,
} from "../core/rational.mjs";
test("rationals reject noncanonical, zero/negative denominators and injection", () => {
  for (const [n, d] of [
    ["7", "0"],
    ["7", "-8"],
    ["07", "8"],
    ["14", "16"],
    ["-0", "1"],
    ["1.2", "3"],
    ["1e2", "3"],
    ["1; sorry", "8"],
    [7, "8"],
    ["1", "01"],
    ["1".repeat(201), "8"],
  ])
    assert.throws(() => rational(n, d));
  assert.deepEqual(rational("-1", "2"), { numerator: "-1", denominator: "2" });
});
test("bounds indistinguishable as floats rank exactly and render without cancellation", () => {
  const a = rational("87499999999999999999", "100000000000000000000"),
    b = rational("43749999999999999999", "50000000000000000000");
  assert.equal(
    Number(a.numerator) / Number(a.denominator),
    Number(b.numerator) / Number(b.denominator),
  );
  assert.equal(cmp(b, a), -1);
  assert.equal(relativePosition(a, b, a), 1);
  assert.equal(relativePosition(b, b, a), 0);
  assert.equal(decimal(sub(BASELINE, a), 22), "0.00000000000000000001");
  assert.equal(log10Rational(sub(BASELINE, a)), -20);
  assert.throws(() => log10Rational(sub(BASELINE, BASELINE)));
});
const records = [
  { id: "a", theta: BASELINE, first_verified_at: "2026-01-01" },
  { id: "b", theta: rational("3", "4"), first_verified_at: "2026-01-02" },
  { id: "c", theta: rational("3", "4"), first_verified_at: "2026-01-03" },
];
test("equal bounds are alternatives and history is immutable", () => {
  const r = recordHistory(records);
  assert.deepEqual(
    r.map((r) => r.is_record),
    [true, true, false],
  );
  const events = [
    { type: "withdraw", id: "b", at: "2026-01-04" },
    { type: "supersede", id: "c", at: "2026-01-05", replacement: "a" },
  ];
  assert.deepEqual(
    activeRecords(records, events).map((r) => r.id),
    ["a"],
  );
  const history = frontierHistory(records, events);
  assert.equal(cmp(history.at(-2).theta, records[1].theta), 0);
  assert.equal(cmp(history.at(-1).theta, BASELINE), 0);
  assert.deepEqual(
    records.map((r) => r.id),
    ["a", "b", "c"],
  );
});
test("records after withdrawal compare to the active frontier while retaining past records", () => {
  const rows = [
    ...records,
    { id: "d", theta: rational("4", "5"), first_verified_at: "2026-01-06" },
  ];
  const events = [
    { type: "withdraw", id: "b", at: "2026-01-04" },
    { type: "withdraw", id: "c", at: "2026-01-05" },
  ];
  assert.equal(recordHistory(rows, events).at(-1).is_record, true);
  assert.equal(recordHistory(rows, events)[1].is_record, true);
});
test("checked bounds above the baseline and tied bounds remain alternatives to the strongest result", () => {
  const best = rational("683505193", "781250000");
  const rows = [
    { id: "baseline", theta: BASELINE, first_verified_at: "2026-01-01" },
    { id: "best", theta: best, first_verified_at: "2026-01-02" },
    {
      id: "single-prime",
      theta: rational("29", "33"),
      first_verified_at: "2026-01-03",
    },
    {
      id: "unit-bound",
      theta: rational("1", "1"),
      first_verified_at: "2026-01-04",
    },
    { id: "tied-best", theta: best, first_verified_at: "2026-01-05" },
  ];
  const history = recordHistory(rows);
  assert.deepEqual(
    history.map((row) => row.is_record),
    [true, true, false, false, false],
  );
  assert.deepEqual(
    history.map((row) => row.record_theta),
    [BASELINE, best, best, best, best],
  );
  assert.deepEqual(
    frontierHistory(rows, []).map((event) => event.theta),
    [BASELINE, best, best, best, best],
  );
  assert.deepEqual(
    activeRecords(rows, []).map((row) => row.id),
    ["baseline", "best", "single-prime", "unit-bound", "tied-best"],
  );
});

test("scientific deltas retain tiny values, sign and three significant digits", () => {
  const cases = [
    ["0", "1", "0"],
    ["1", "4", "2.5e-1"],
    ["-1", "10", "-1e-1"],
    ["1", "3", "3.33e-1"],
    ["9999", "10000", "1e+0"],
    ["100", "1", "1e+2"],
    ["1", "1" + "0".repeat(400), "1e-400"],
  ];
  for (const [numerator, denominator, expected] of cases)
    assert.equal(scientific({ numerator, denominator }), expected);
});
