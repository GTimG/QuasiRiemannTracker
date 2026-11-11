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

// QRH-Decimal is an accurate truncation of the ranked rational bound. A bound
// equal to or above the current best is admitted as it is; a bound below it
// must be distinguishably lower within the declared digits.
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
  const best = catalogue.records
    .filter(verifiedHere)
    .reduce(
      (best, record) =>
        !best || cmp(checkedRational(record.theta), best.theta) < 0
          ? record
          : best,
      null,
    );
  if (
    best &&
    cmp(candidate, best.theta) < 0 &&
    prefix(best.theta, digits) === actual
  )
    throw Error(
      `QRH-Decimal needs more digits to show the bound is below the current best (${best.id}: ${actual})`,
    );
}
