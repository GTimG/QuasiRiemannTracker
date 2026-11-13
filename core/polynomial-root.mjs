import { rational, cmp, gcd } from "./rational.mjs";

// Ascending integer coefficients and an open rational isolating interval.
// Parsing establishes syntax only. Comparator checks existence AND uniqueness
// in Lean, in addition to nonvanishing and the rational upper comparison.
export function polynomialRoot(label) {
  if (typeof label !== "string" || label.length > 256)
    throw Error("Polynomial root expression is missing or too long");
  const match = /^root\(\[([^\]]+)\],(-?\d+\/\d+),(-?\d+\/\d+)\)$/.exec(label);
  if (!match) throw Error("Use root([c0,c1,...,cn],lower,upper)");
  const coefficients = match[1].split(",");
  if (
    coefficients.length < 3 ||
    coefficients.length > 33 ||
    coefficients.some((c) => !/^(?:0|-?[1-9]\d{0,199})$/.test(c))
  )
    throw Error("Use 3 to 33 canonical integer coefficients");
  const values = coefficients.map(BigInt);
  if (values.at(-1) <= 0n || values.reduce((g, c) => gcd(g, c), 0n) !== 1n)
    throw Error(
      "Polynomial must be primitive with positive leading coefficient",
    );
  const read = (s) => rational(...s.split("/"));
  const lower = read(match[2]),
    upper = read(match[3]);
  if (cmp(lower, upper) >= 0) throw Error("Root interval must be increasing");
  const number = (c) => (c.startsWith("-") ? `(${c})` : c);
  const horner = coefficients.reduceRight(
    (rest, c) => (rest === null ? number(c) : `(${number(c)} + x * ${rest})`),
    null,
  );
  const endpoint = (r) => `(${r.numerator} / ${r.denominator})`;
  const predicate = `${endpoint(lower)} < x ∧ x < ${endpoint(upper)} ∧ ${horner} = 0`;
  return {
    label,
    lean: `sInf {x | ${predicate}}`,
    isolation_lean: `∃! x : ℝ, ${predicate}`,
  };
}

// Accept only the generated Lean spelling, modulo whitespace. Never splice
// arbitrary source text into a challenge.
export function polynomialRootFromLean(text) {
  const compact = text.replace(/\s/g, "");
  const match =
    /^sInf\{x\|\((-?\d+)\/(\d+)\)<x∧x<\((-?\d+)\/(\d+)\)∧(.+)=0\}$/.exec(
      compact,
    );
  if (!match) throw Error("Malformed polynomial root in Lean source");
  const coefficients = match[5].match(/-?\d+/g) ?? [];
  const root = polynomialRoot(
    `root([${coefficients.join(",")}],${match[1]}/${match[2]},${match[3]}/${match[4]})`,
  );
  if (root.lean.replace(/\s/g, "") !== compact)
    throw Error("Use the generated Horner spelling for a polynomial root");
  return root;
}
