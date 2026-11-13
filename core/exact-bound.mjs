import { fraction, rational } from "./rational.mjs";
import { polynomialRoot, polynomialRootFromLean } from "./polynomial-root.mjs";

// A bound is identified by one canonical string, `theta_exact`:
//
//   p/q              a reduced fraction, proved directly; or
//   EXPR ≤ p/q       an exact algebraic expression EXPR, proved in Lean
//                    together with the rational upper bound EXPR ≤ p/q.
//
// The rational p/q is the value that is ranked and shown on the leaderboard.
// EXPR is the exact statement; Comparator checks both theorems, so neither
// side relies on verifier arithmetic. Submitted text is parsed and re-rendered
// from integers; it is never interpolated into Lean code.
//
// EXPR is built from integer literals with + − * / and √, where √ applies to
// a positive integer literal and / divides by a positive integer literal.
// These are exactly the expressions whose Lean semantics (Real.sqrt, real
// division) agree with ordinary arithmetic. Juxtaposition `k√n` means k * √n.

export const RATIONAL_TARGET = "QRH.canonical_bound_le";
export const RATIONAL_DECLARATION = "Candidate.bound_le";
const MAX_EXPRESSION = 256;
const SEPARATOR = " ≤ ";

const TOKEN = {
  label: /\s*(?:(\d+)|(√)|([-−+*/()]))/y,
  lean: /\s*(?:(\d+)|(Real\.sqrt)\b|([-+*/()]))/y,
};

function tokens(text, syntax) {
  const pattern = TOKEN[syntax],
    out = [];
  pattern.lastIndex = 0;
  while (pattern.lastIndex < text.length) {
    if (/^\s*$/.test(text.slice(pattern.lastIndex))) break;
    const start = pattern.lastIndex;
    const match = pattern.exec(text);
    if (!match) throw Error(`Unsupported symbol in exact bound: ${text}`);
    const value =
      match[1] ?? (match[2] ? "√" : match[3] === "−" ? "-" : match[3]);
    // A label coefficient k√n is written without a space.
    const glued = start > 0 && !/^\s/.test(match[0]);
    out.push({ value, int: match[1] !== undefined, glued });
  }
  return out;
}

function parse(text, syntax) {
  if (typeof text !== "string" || !text || text.length > MAX_EXPRESSION)
    throw Error("Exact bound expression is missing or too long");
  const list = tokens(text, syntax);
  let i = 0;
  const peek = () => list[i]?.value;
  const take = (value) => {
    if (peek() !== value) throw Error(`Malformed exact bound: ${text}`);
    i++;
  };
  const integer = () => {
    const token = list[i++];
    if (!token?.int || !/^(?:0|[1-9]\d{0,199})$/.test(token.value))
      throw Error(`Malformed exact bound: ${text}`);
    return { kind: "int", value: token.value };
  };
  const sqrt = () => {
    take("√");
    const radicand = integer();
    if (radicand.value === "0")
      throw Error("√ applies to a positive integer literal");
    return { kind: "sqrt", radicand };
  };
  const factor = () => {
    if (peek() === "(") {
      take("(");
      const inner = expression();
      take(")");
      return inner;
    }
    if (peek() === "√") return sqrt();
    const value = integer();
    if (syntax === "label" && peek() === "√" && list[i].glued)
      return { kind: "*", left: value, right: sqrt() };
    return value;
  };
  const term = () => {
    let left = factor();
    while (peek() === "*" || peek() === "/") {
      const kind = list[i++].value;
      const right = factor();
      if (kind === "/" && (right.kind !== "int" || right.value === "0"))
        throw Error("Divide only by a positive integer literal");
      left = { kind, left, right };
    }
    return left;
  };
  const expression = () => {
    let left = term();
    while (peek() === "+" || peek() === "-")
      left = { kind: list[i++].value, left, right: term() };
    return left;
  };
  const tree = expression();
  if (i !== list.length) throw Error(`Malformed exact bound: ${text}`);
  return tree;
}

const PRECEDENCE = { "+": 1, "-": 1, "*": 2, "/": 2 };
function render(node, syntax) {
  if (node.kind === "int") return node.value;
  if (node.kind === "sqrt")
    return syntax === "label"
      ? `√${node.radicand.value}`
      : `Real.sqrt ${node.radicand.value}`;
  if (
    syntax === "label" &&
    node.kind === "*" &&
    node.left.kind === "int" &&
    node.right.kind === "sqrt"
  )
    return `${node.left.value}${render(node.right, syntax)}`;
  const side = (child, right) => {
    const text = render(child, syntax);
    const p = PRECEDENCE[child.kind];
    return p &&
      (p < PRECEDENCE[node.kind] || (right && p === PRECEDENCE[node.kind]))
      ? `(${text})`
      : text;
  };
  const op = syntax === "label" && node.kind === "-" ? "−" : node.kind;
  return `${side(node.left, false)} ${op} ${side(node.right, true)}`;
}

const hasSqrt = (node) =>
  node.kind === "sqrt" ||
  (node.left !== undefined && (hasSqrt(node.left) || hasSqrt(node.right)));

function algebraic(tree) {
  if (!hasSqrt(tree))
    throw Error("An exact bound without √ is rational: submit the fraction");
  return { label: render(tree, "label"), lean: render(tree, "lean") };
}

// The canonical label of a submitted exact expression. Other spellings are
// rejected with the canonical one, so equal bounds always have equal labels.
export function algebraicExpression(label) {
  if (label.startsWith("root(")) return polynomialRoot(label);
  const expression = algebraic(parse(label, "label"));
  if (expression.label !== label)
    throw Error(`Write the exact bound canonically as ${expression.label}`);
  return expression;
}

// Read an expression from Lean source (whitespace-insensitive).
export function algebraicFromLean(text) {
  if (text.trimStart().startsWith("sInf")) return polynomialRootFromLean(text);
  return algebraic(parse(text, "lean"));
}

function positiveFraction(text) {
  const match = /^(-?\d+)\/(\d+)$/.exec(text ?? "");
  if (!match) return null;
  const theta = rational(match[1], match[2]);
  if (BigInt(theta.numerator) <= 0n) throw Error("Bound must be positive");
  return theta;
}

export const witnessedBound = (label, theta) =>
  `${label}${SEPARATOR}${fraction(theta)}`;

export function exactBound(theta_exact) {
  const theta = positiveFraction(theta_exact);
  if (theta)
    return {
      theta_exact,
      theta,
      lean: `${theta.numerator} / ${theta.denominator}`,
    };
  const parts = (theta_exact ?? "").split(SEPARATOR);
  const witness = parts.length === 2 && positiveFraction(parts[1]);
  if (!witness)
    throw Error(
      "Use a reduced fraction p/q, or an exact expression with a rational upper bound: EXPR ≤ p/q",
    );
  const expression = algebraicExpression(parts[0]);
  return {
    theta_exact,
    theta: witness,
    exact_bound: expression.label,
    lean: expression.lean,
    rational_lean: `${witness.numerator} / ${witness.denominator}`,
    ...(expression.isolation_lean
      ? { isolation_lean: expression.isolation_lean }
      : {}),
  };
}

// Comparator targets that together establish theta_exact.
export const boundTargets = (theta_exact) => [
  "QRH.canonical_bound",
  ...(exactBound(theta_exact).rational_lean ? [RATIONAL_TARGET] : []),
  ...(exactBound(theta_exact).isolation_lean
    ? ["QRH.canonical_bound_isolated"]
    : []),
];
