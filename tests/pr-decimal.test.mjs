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
    "01.0",
    "-1.0",
    "1",
    "1.",
    `${"1".repeat(201)}.0`,
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

test("an equal exact bound accepts an accurate decimal at any precision", () => {
  for (const theta_decimal of ["0.8", "0.87488664704", "0.8748866470400"])
    assert.deepEqual(
      check({
        theta_exact: "683505193/781250000",
        theta_decimal,
      }),
      { previous_result_id: "current", previous_decimal: theta_decimal },
    );
  assert.throws(
    () => check({ theta_exact: "683505193/781250000", theta_decimal: "0.9" }),
    {
      message: "QRH-Decimal must give the exact bound's truncated digits: 0.8",
    },
  );
});

test("verified alternative bounds include 29/33 and the historical theta-one bound", () => {
  for (const [theta_exact, theta_decimal, previous_decimal] of [
    ["7/8", "0.875", "0.874"],
    ["29/33", "0.87878787", "0.874"],
    ["1/1", "1.0", "0"],
    ["2/1", "2.000", "0"],
  ])
    assert.deepEqual(check({ theta_exact, theta_decimal }), {
      previous_result_id: "current",
      previous_decimal,
    });
  assert.throws(() => check({ theta_exact: "29/33", theta_decimal: "0.87" }), {
    message:
      "QRH-Decimal needs more digits to differ from the previous bound (current: 0.87)",
  });
});

test("integer parts and fractional precision are compared exactly", () => {
  const whole = "12345678901234567890123456789";
  assert.equal(decimalPrecision(`${whole}.1`), 1);
  assert.equal(decimalPrecision("12.030"), 3);
  assert.deepEqual(
    check({
      theta_exact: `${whole}1/10`,
      theta_decimal: `${whole}.1`,
      catalogue: { records: [record("large", q(whole, "1"))] },
    }),
    { previous_result_id: "large", previous_decimal: `${whole}.0` },
  );
  assert.deepEqual(
    check({ catalogue: { records: [record("historical", q("1", "1"))] } }),
    { previous_result_id: "historical", previous_decimal: "1" },
  );
  assert.throws(() => check({ theta_exact: "1/1", theta_decimal: "1.1" }), {
    message: "QRH-Decimal must give the exact bound's truncated digits: 1.0",
  });
});

const algebraic = {
  theta_exact: "sqrt(3)/2",
  theta_decimal: "0.866",
  bound_interval: {
    lower: q("433", "500"),
    upper: q("8661", "10000"),
  },
};

test("a smaller bound sharing all 200 digits is compared exactly", () => {
  const n = 10n ** 110n;
  const smaller = {
    theta_exact: `${n - 1n}/${3n * n - 2n}`,
    theta_decimal: `0.${((n - 1n) * 10n ** 200n) / (3n * n - 2n)}`,
    catalogue: { records: [record("previous", q(`${n}`, `${3n * n + 1n}`))] },
  };
  assert.deepEqual(check(smaller), {
    previous_result_id: "previous",
    previous_decimal: smaller.theta_decimal,
  });
  const shorter = smaller.theta_decimal.slice(0, -1);
  assert.throws(
    () => check({ ...smaller, theta_decimal: shorter }),
    /more digits/,
  );
});

test("an irrational uses the enclosure in the trusted receipt", () => {
  assert.doesNotThrow(() => check(algebraic));
  assert.throws(
    () => check({ ...algebraic, theta_decimal: "0.8660" }),
    /bound_interval needs refinement/,
  );
});

test("an irrational above one uses its certified enclosure", () => {
  assert.deepEqual(
    check({
      theta_exact: "sqrt(2)",
      theta_decimal: "1.4142",
      bound_interval: {
        lower: q("141421", "100000"),
        upper: q("70711", "50000"),
      },
    }),
    { previous_result_id: "current", previous_decimal: "0" },
  );
});

test("a certified integer difference establishes distinct bounds", () => {
  assert.deepEqual(
    check({
      theta_exact: "1/1",
      theta_decimal: "1.0",
      catalogue: {
        records: [
          record("algebraic", q("99", "100"), {
            exact_bound: "sqrt(3)/2",
            bound_interval: { lower: q("81", "100"), upper: q("99", "100") },
          }),
        ],
      },
    }),
    { previous_result_id: "algebraic", previous_decimal: "0" },
  );
});

test("a nonpositive rational fails positivity even when an enclosure is supplied", () => {
  for (const theta_exact of ["0/1", "-1/1"])
    assert.throws(
      () =>
        check({
          theta_exact,
          theta_decimal: "0.8",
          bound_interval: { lower: q("4", "5"), upper: q("4", "5") },
        }),
      { message: "Decimal comparison bounds must be positive" },
    );
});

test("rejects missing, reversed or nonpositive irrational enclosures", () => {
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
  for (const lower of [q("0", "1"), q("-1", "2")])
    assert.throws(
      () => check({ ...algebraic, bound_interval: { lower, upper: lower } }),
      { message: "Decimal comparison bounds must be positive" },
    );
});

test("rational syntax and normalization stay exact", () => {
  for (const theta_exact of ["2/4", "01/2", "1/0", "0/1"])
    assert.throws(() => check({ theta_exact }));
});

test("the comparison uses the best currently verified catalogue bound", () => {
  assert.deepEqual(
    check({
      catalogue: {
        records: [
          record("older", q("7", "8")),
          record("alternative", q("29", "33")),
          record("historical-baseline", q("1", "1")),
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
  assert.deepEqual(check({ ...algebraic, catalogue }), {
    previous_result_id: "algebraic",
    previous_decimal: "0.866",
  });
  assert.deepEqual(
    check({
      ...algebraic,
      theta_decimal: "0.86602",
      bound_interval: {
        lower: q("4330127", "5000000"),
        upper: q("34641017", "40000000"),
      },
      catalogue,
    }),
    { previous_result_id: "algebraic", previous_decimal: "0.86602" },
  );
});

test("requires a previously accepted or verified catalogue bound", () => {
  assert.throws(() => check({ catalogue: {} }), /trusted catalogue/);
  assert.throws(
    () => check({ catalogue: { records: [] } }),
    /requires a previously accepted or verified catalogue bound/,
  );
  assert.throws(
    () =>
      check({
        catalogue: {
          records: [{ ...current, status: "verification-pending" }],
        },
      }),
    /requires a previously accepted or verified catalogue bound/,
  );
});

test("accepted sources supply the previous decimal bound without a verification receipt", () => {
  const accepted = { ...current, status: "accepted", first_verified_at: "" };
  assert.deepEqual(check({ catalogue: { records: [accepted] } }), {
    previous_result_id: "current",
    previous_decimal: "0.87488664",
  });
  assert.throws(
    () =>
      check({ theta_decimal: "0.8748866", catalogue: { records: [accepted] } }),
    /more digits/,
  );
});
