import { cmp, rational } from "../core/rational.mjs";
import { verifiedHere } from "../core/catalogue.mjs";

export function decimalPrecision(value) {
  if (
    typeof value !== "string" ||
    value !== value.trim() ||
    !/^(?:0|[1-9]\d{0,199})\.\d{1,200}$/.test(value)
  )
    throw Error(
      "QRH-Decimal must have a canonical integer part and 1–200 fractional digits",
    );
  return value.length - value.indexOf(".") - 1;
}

function checkedRational(value) {
  const result = rational(value?.numerator, value?.denominator);
  if (BigInt(result.numerator) <= 0n)
    throw Error("Decimal comparison bounds must be positive");
  return result;
}

function interval(value, label) {
  if (!value || typeof value !== "object" || !value.lower || !value.upper)
    throw Error(`${label} needs a trusted certified bound_interval`);
  const lower = checkedRational(value.lower),
    upper = checkedRational(value.upper);
  if (cmp(lower, upper) > 0) throw Error(`${label} bound_interval is reversed`);
  return { lower, upper };
}

function singleton(value) {
  const exact = checkedRational(value);
  return { lower: exact, upper: exact };
}

function prefix(bounds, digits, label) {
  const scale = 10n ** BigInt(digits);
  const scaled = (q) => (BigInt(q.numerator) * scale) / BigInt(q.denominator);
  const lower = scaled(bounds.lower),
    upper = scaled(bounds.upper);
  if (lower !== upper)
    throw Error(
      `${label} bound_interval needs refinement to certify these decimal digits`,
    );
  return digits === 0
    ? String(lower)
    : `${lower / scale}.${String(lower % scale).padStart(digits, "0")}`;
}

// Compare rational bounds and certified algebraic enclosures from the trusted
// base checkout's verification records and catalogue.
export function validateDecimalApproximation({
  theta_exact,
  theta_decimal,
  bound_interval,
  catalogue,
}) {
  const digits = decimalPrecision(theta_decimal);
  if (
    typeof theta_exact !== "string" ||
    !theta_exact ||
    theta_exact !== theta_exact.trim()
  )
    throw Error("A decimal approximation needs an exact bound");
  const match = /^(-?\d+)\/(\d+)$/.exec(theta_exact);
  const candidate = match
    ? singleton(rational(match[1], match[2]))
    : interval(bound_interval, "The exact algebraic bound");
  const actual = prefix(candidate, digits, "The submitted bound");
  if (actual !== theta_decimal)
    throw Error(
      `QRH-Decimal must give the exact bound's truncated digits: ${actual}`,
    );

  if (!Array.isArray(catalogue?.records))
    throw Error("A trusted catalogue is required for decimal comparison");
  const verified = catalogue.records.filter(verifiedHere);
  if (!verified.length)
    throw Error(
      "Decimal comparison requires a previously accepted or verified catalogue bound",
    );
  const previous = verified.reduce((best, record) => {
    checkedRational(record.theta);
    return !best || cmp(record.theta, best.theta) < 0 ? record : best;
  }, null);
  const previousBounds = previous.exact_bound
    ? interval(previous.bound_interval, "The previous bound")
    : singleton(previous.theta);
  if (
    theta_exact === previous.exact_bound ||
    (cmp(candidate.lower, candidate.upper) === 0 &&
      cmp(previousBounds.lower, previousBounds.upper) === 0 &&
      cmp(candidate.lower, previousBounds.lower) === 0)
  )
    return {
      previous_result_id: previous.id,
      previous_decimal: actual,
    };
  // The previous bound needs certified digits through the first difference.
  const fractionalStart = actual.indexOf(".") + 1;
  for (let places = 0; places <= digits; places++) {
    const previousDecimal = prefix(
      previousBounds,
      places,
      "The previous bound",
    );
    const candidateDecimal = actual.slice(
      0,
      places === 0 ? fractionalStart - 1 : fractionalStart + places,
    );
    if (candidateDecimal !== previousDecimal)
      return {
        previous_result_id: previous.id,
        previous_decimal: previousDecimal,
      };
  }
  throw Error(
    `QRH-Decimal needs more digits to differ from the previous bound (${previous.id}: ${actual})`,
  );
}
