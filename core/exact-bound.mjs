import { rational } from "./rational.mjs";

// Canonical algebraic expressions are fixed verifier profiles. Submitted text
// is matched exactly; it is never interpolated into Lean code.
const liu = {
  a: 1507,
  b: -2,
  c: 921,
  d: 1653,
  interval: {
    lower: {
      numerator: "437478534899584370009170003479",
      denominator: "500000000000000000000000000000",
    },
    upper: {
      numerator: "874957069799168740018340006959",
      denominator: "1000000000000000000000000000000",
    },
  },
};

const liu_b2 = {
  a: 777,
  b: -1,
  c: 1081,
  d: 852,
  interval: {
    lower: {
      numerator:
        "24688254145074084030172790155815084825965998942550936221513452062089675469831194293805185151144250024225192359013041730108629663",
      denominator:
        "28267419169198061992769170562799551248696516910546746098830919495493448867291560772223652902664903495976081554351489835815165175",
    },
    upper: {
      numerator:
        "63123118504693955254447460018494773970235238755621464746402012449092091902425088889000654796282104118233737075161076112087901328",
      denominator:
        "72274355227956214899270016096943249636058769070465791728289056882829577892844484301278423569693839288110933352950546632116849073",
    },
  },
};

// Each profile is x = (a + b*sqrt(c)) / d with b < 0, keyed by its label.
export const algebraicProfiles = new Map(
  [liu, liu_b2].map((p) => {
    const k = p.b === -1 ? "" : -p.b;
    const label = `(${p.a} − ${k}√${p.c}) / ${p.d}`;
    const lean = `(${p.a} - ${k}${k && " * "}Real.sqrt ${p.c}) / ${p.d}`;
    return [label, { ...p, label, lean }];
  }),
);

// For r = p/q, x > r iff a*q - d*p > 0 and (a*q - d*p)^2 > b^2*c*q^2.
// The result has the sign of x - r.
export function algebraicDelta({ a, b, c, d }, r) {
  const p = BigInt(r.numerator),
    q = BigInt(r.denominator),
    lhs = BigInt(a) * q - BigInt(d) * p;
  if (lhs <= 0n) throw Error("Algebraic interval outside positive branch");
  return lhs * lhs - BigInt(b * b * c) * q * q;
}

export function exactBound(label) {
  const fraction = /^(\d+)\/(\d+)$/.exec(label ?? "");
  if (fraction) {
    const theta = rational(fraction[1], fraction[2]);
    if (BigInt(theta.numerator) <= 0n) throw Error("Bound must be positive");
    return { theta, lean: `${theta.numerator} / ${theta.denominator}` };
  }
  const profile = algebraicProfiles.get(label);
  if (profile) {
    if (
      algebraicDelta(profile, profile.interval.lower) <= 0n ||
      algebraicDelta(profile, profile.interval.upper) >= 0n
    )
      throw Error("Invalid algebraic profile enclosure");
    return {
      theta: structuredClone(profile.interval.upper),
      exact_bound: profile.label,
      bound_interval: structuredClone(profile.interval),
      lean: profile.lean,
    };
  }
  throw Error("This exact expression requires an algebraic checking profile");
}
