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
