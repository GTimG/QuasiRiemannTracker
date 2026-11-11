import { cmp, rational } from "../core/rational.mjs";
import { verifiedHere } from "../core/catalogue.mjs";
import { exactBound } from "../core/exact-bound.mjs";

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

// Truncated decimal digits of a positive rational.
function prefix(q, digits) {
  const scale = 10n ** BigInt(digits);
  const scaled = (BigInt(q.numerator) * scale) / BigInt(q.denominator);
  return digits === 0
    ? String(scaled)
    : `${scaled / scale}.${String(scaled % scale).padStart(digits, "0")}`;
}

// Every ranked bound is rational (an exact expression is ranked by its proved
// rational upper bound), so decimals are compared against the trusted base
// checkout's catalogue exactly.
export function validateDecimalApproximation({
  theta_exact,
  theta_decimal,
  catalogue,
}) {
  const digits = decimalPrecision(theta_decimal);
  if (
    typeof theta_exact !== "string" ||
    !theta_exact ||
    theta_exact !== theta_exact.trim()
  )
    throw Error("A decimal approximation needs an exact bound");
  const candidate = checkedRational(exactBound(theta_exact).theta);
  const actual = prefix(candidate, digits);
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
  if (cmp(candidate, previous.theta) === 0)
    return { previous_result_id: previous.id, previous_decimal: actual };
  // Report the previous bound through the first differing digit.
  const fractionalStart = actual.indexOf(".") + 1;
  for (let places = 0; places <= digits; places++) {
    const previousDecimal = prefix(previous.theta, places);
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
