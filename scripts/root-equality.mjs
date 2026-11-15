// Integer polynomials have ascending coefficients. Divide out only positive
// content: Sturm variations depend on the signs of the remainders.
import { cmp, gcd } from "../core/rational.mjs";

function primitive(poly) {
  while (poly.length && poly.at(-1) === 0n) poly.pop();
  const content = poly.reduce(gcd, 0n);
  return content > 1n ? poly.map((c) => c / content) : poly;
}

function remainder(a, b) {
  const lead = b.at(-1);
  const scale = lead < 0n ? -lead : lead;
  while (a.length >= b.length) {
    const shift = a.length - b.length;
    const factor = lead < 0n ? -a.at(-1) : a.at(-1);
    a = primitive(a.map((c, i) => c * scale - (b[i - shift] ?? 0n) * factor));
  }
  return a;
}

function derivative(p) {
  return p.slice(1).map((c, i) => c * BigInt(i + 1));
}

// Sign of p(n/d) without rational rounding or division.
export function signAt(p, { numerator, denominator }) {
  const n = BigInt(numerator),
    d = BigInt(denominator);
  let value = 0n,
    power = 1n;
  for (let i = p.length - 1; i >= 0; i--) {
    value = value * n + p[i] * power;
    power *= d;
  }
  return value < 0n ? -1 : value > 0n ? 1 : 0;
}

// Sign just inside an open endpoint, including zeros of higher multiplicity.
function interiorSign(poly, point, direction) {
  let sign = 1;
  for (let p = poly; p.length; p = derivative(p)) {
    const value = signAt(p, point);
    if (value) return sign * value;
    sign *= direction;
  }
  throw Error("Zero polynomial in Sturm sequence");
}

export function sameRoot(a, b) {
  const lo = cmp(a.lower, b.lower) >= 0 ? a.lower : b.lower;
  const hi = cmp(a.upper, b.upper) <= 0 ? a.upper : b.upper;
  if (cmp(lo, hi) >= 0) return false;

  // A common root in the intersection must be the uniquely isolated root
  // of both verified statements. Their polynomials need not be irreducible.
  let p = a.coefficients,
    q = b.coefficients;
  while (q.length) [p, q] = [q, remainder(p, q)];
  if (p.length < 2) return false;
  let previousLeft = 0,
    previousRight = 0,
    count = 0;
  q = derivative(p);
  while (p.length) {
    const left = interiorSign(p, lo, 1);
    const right = interiorSign(p, hi, -1);
    if (previousLeft * left < 0) count++;
    if (previousRight * right < 0) count--;
    previousLeft = left;
    previousRight = right;
    [p, q] = [q, q.length ? remainder(p, q).map((c) => -c) : []];
  }
  return count > 0;
}
