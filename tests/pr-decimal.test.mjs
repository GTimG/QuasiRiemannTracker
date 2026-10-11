import test from "node:test";
import assert from "node:assert/strict";
import {
  decimalPrecision,
  validateDecimalApproximation,
} from "../verifier/pr-decimal.mjs";

const q = (numerator, denominator) => ({ numerator, denominator });
const record = (id, theta, extra = {}) => ({
  id,
  theta,
  status: "framework-verified",
  ...extra,
});
const current = record("current", q("683505193", "781250000"));
const options = (extra = {}) => ({
  theta_exact: "4374433/5000000",
  theta_decimal: "0.87488660",
  catalogue: { records: [current] },
  ...extra,
});
const check = (extra) => validateDecimalApproximation(options(extra));

test("a required decimal extends through the first differing digit", () => {
  assert.equal(decimalPrecision("0.87488660"), 8);
  assert.deepEqual(check(), {
    previous_result_id: "current",
    previous_decimal: "0.87488664",
  });
  assert.throws(() => check({ theta_decimal: "0.8748866" }), /more digits/);
});

test("rejects missing, malformed and excessively long decimals", () => {
  for (const theta_decimal of [
    undefined,
    null,
    0.8748866,
    "",
    "0",
    "0.",
    ".87488660",
    "00.87488660",
    "0.87488660…",
    "8.748866e-1",
    "+0.87488660",
    " 0.87488660",
    "0.87488660\n",
    `0.${"8".repeat(201)}`,
  ]) {
    assert.throws(() => decimalPrecision(theta_decimal), /QRH-Decimal/);
    assert.throws(() => check({ theta_decimal }), /QRH-Decimal/);
  }
});

test("rejects fabricated decimal digits", () => {
  assert.throws(
    () => check({ theta_decimal: "0.87488661" }),
    /truncated digits/,
  );
  assert.throws(() => check({ theta_decimal: "0.7" }), /truncated digits/);
});

test("a terminating rational may include trailing zeroes", () => {
  assert.doesNotThrow(() =>
    check({ theta_decimal: `0.8748866${"0".repeat(193)}` }),
  );
});

test("comparison remains exact well beyond floating-point precision", () => {
  const denominator = `1${"0".repeat(30)}`;
  const numerator = "874886647039999999999999999999";
  assert.equal(Number(`0.${numerator}`), Number("0.87488664704"));
  assert.doesNotThrow(() =>
    check({
      theta_exact: `${numerator}/${denominator}`,
      theta_decimal: `0.${numerator}`,
    }),
  );
  const shared = "87488664704000000000000000000";
  const farther = q(`${shared}3`, denominator);
  assert.throws(
    () =>
      check({
        theta_exact: `${shared}1/${denominator}`,
        theta_decimal: `0.${shared}`,
        catalogue: { records: [record("farther", farther)] },
      }),
    /more digits/,
  );
  assert.doesNotThrow(() =>
    check({
      theta_exact: `${shared}1/${denominator}`,
      theta_decimal: `0.${shared}1`,
      catalogue: { records: [record("farther", farther)] },
    }),
  );
});

test("validates decimal digits by truncation", () => {
  assert.doesNotThrow(() =>
    check({ theta_exact: "874886599/1000000000", theta_decimal: "0.8748865" }),
  );
  assert.throws(
    () =>
      check({
        theta_exact: "874886599/1000000000",
        theta_decimal: "0.8748866",
      }),
    /truncated digits/,
  );
});

test("requires an exact bound distinct from the previous bound", () => {
  assert.throws(
    () =>
      check({
        theta_exact: "683505193/781250000",
        theta_decimal: "0.87488664704",
      }),
    /equals the previous bound/,
  );
});

test("accepts a distinct bound larger than the current record", () => {
  assert.doesNotThrow(() =>
    check({ theta_exact: "7/8", theta_decimal: "0.875" }),
  );
});

const algebraic = {
  theta_exact: "sqrt(3)/2",
  theta_decimal: "0.866",
  bound_interval: {
    lower: q("433", "500"),
    upper: q("8661", "10000"),
  },
};

test("an irrational uses the enclosure in the trusted receipt", () => {
  assert.doesNotThrow(() => check(algebraic));
  assert.throws(
    () => check({ ...algebraic, theta_decimal: "0.8660" }),
    /bound_interval needs refinement/,
  );
});

test("rejects missing, reversed or out-of-range irrational enclosures", () => {
  for (const bound_interval of [undefined, {}, { lower: q("1", "2") }])
    assert.throws(
      () => check({ ...algebraic, bound_interval }),
      /bound_interval/,
    );
  assert.throws(
    () =>
      check({
        ...algebraic,
        bound_interval: {
          lower: algebraic.bound_interval.upper,
          upper: algebraic.bound_interval.lower,
        },
      }),
    /reversed/,
  );
  for (const lower of [q("0", "1"), q("-1", "2"), q("9", "10")])
    assert.throws(() =>
      check({ ...algebraic, bound_interval: { lower, upper: lower } }),
    );
});

test("rational syntax and normalization stay exact", () => {
  for (const theta_exact of ["2/4", "01/2", "1/0", "9/10", "0/1"])
    assert.throws(() => check({ theta_exact }));
});

test("the comparison uses the best currently verified catalogue bound", () => {
  assert.deepEqual(
    check({
      catalogue: {
        records: [
          record("older", q("7", "8")),
          record("pending", q("1", "2"), { status: "verification-pending" }),
          current,
        ],
        historical_records: [record("historical", q("1", "4"))],
      },
    }),
    { previous_result_id: "current", previous_decimal: "0.87488664" },
  );
});

test("certifies previous irrational digits through the first difference", () => {
  const catalogue = {
    records: [
      record("algebraic", algebraic.bound_interval.upper, {
        exact_bound: algebraic.theta_exact,
        bound_interval: algebraic.bound_interval,
      }),
    ],
  };
  assert.doesNotThrow(() =>
    check({ theta_exact: "4/5", theta_decimal: "0.800", catalogue }),
  );
  assert.deepEqual(
    check({ theta_exact: "4/5", theta_decimal: "0.8000", catalogue }),
    { previous_result_id: "algebraic", previous_decimal: "0.86" },
  );
  assert.throws(
    () =>
      check({
        theta_exact: "17321/20000",
        theta_decimal: "0.86605",
        catalogue,
      }),
    /previous bound.*bound_interval needs refinement/,
  );
  assert.throws(
    () => check({ ...algebraic, catalogue }),
    /equals the previous/,
  );
});

test("requires a previously verified catalogue bound", () => {
  assert.throws(() => check({ catalogue: {} }), /trusted catalogue/);
  assert.throws(
    () => check({ catalogue: { records: [] } }),
    /requires a previously verified catalogue bound/,
  );
  assert.throws(
    () =>
      check({
        catalogue: {
          records: [{ ...current, status: "verification-pending" }],
        },
      }),
    /requires a previously verified catalogue bound/,
  );
});
