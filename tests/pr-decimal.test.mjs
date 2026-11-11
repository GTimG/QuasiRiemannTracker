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

test("a lower bound must be lower within its declared digits", () => {
  assert.equal(decimalPrecision("0.87488660"), 8);
  assert.doesNotThrow(() => check());
  assert.throws(() => check({ theta_decimal: "0.8748866" }), {
    message:
      "QRH-Decimal needs more digits to show the bound is below the current best (current: 0.8748866)",
  });
});

test("equal and larger bounds accept an accurate decimal at any precision", () => {
  for (const [theta_exact, theta_decimal] of [
    ["683505193/781250000", "0.8"],
    ["683505193/781250000", "0.87488664704"],
    ["7/8", "0.8"],
    ["(777 − √1081) / 852 ≤ 7/8", "0.875"],
    ["2/1", "2.0"],
  ])
    assert.doesNotThrow(() => check({ theta_exact, theta_decimal }));
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

test("integer parts and fractional precision are compared exactly", () => {
  const whole = "12345678901234567890123456789";
  assert.equal(decimalPrecision(`${whole}.1`), 1);
  assert.equal(decimalPrecision("12.030"), 3);
  assert.throws(() => check({ theta_exact: "1/1", theta_decimal: "1.1" }), {
    message: "QRH-Decimal must give the exact bound's truncated digits: 1.0",
  });
});

test("a nonpositive rational fails positivity", () => {
  for (const theta_exact of ["0/1", "-1/1"])
    assert.throws(() => check({ theta_exact, theta_decimal: "0.8" }), {
      message: "Bound must be positive",
    });
});

test("rational syntax and normalization stay exact", () => {
  for (const theta_exact of ["2/4", "01/2", "1/0", "0/1"])
    assert.throws(() => check({ theta_exact }));
});

test("the comparison uses the best accepted or verified catalogue bound", () => {
  const records = [
    record("older", q("7", "8")),
    record("pending", q("1", "2"), { status: "verification-pending" }),
    { ...current, status: "accepted", first_verified_at: "" },
  ];
  assert.throws(
    () => check({ theta_decimal: "0.8748866", catalogue: { records } }),
    /below the current best \(current/,
  );
  assert.doesNotThrow(() => check({ catalogue: { records: [] } }));
  assert.throws(() => check({ catalogue: {} }), /trusted catalogue/);
});
