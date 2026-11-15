// Catalogue-only annotations, computed after certificate validation. The
// submitted expression and its ranked rational witness stay bound to the receipt.
import { parsePolynomialRoot } from "../core/polynomial-root.mjs";
import { cmp } from "../core/rational.mjs";
import { sameRoot, signAt } from "./root-equality.mjs";
import {
  radicalValue,
  rationalValue,
  equalValues,
  rootEqualsRadical,
} from "./radical-value.mjs";

function endpoint(record) {
  if (!record.exact_bound) return { rational: record.theta };
  if (record.exact_bound.startsWith("root(")) {
    const root = parsePolynomialRoot(record.exact_bound);
    return { root: { ...root, coefficients: root.coefficients.map(BigInt) } };
  }
  return { radical: radicalValue(record.exact_bound) };
}

function equal(a, b) {
  if (a.rational && b.rational) return cmp(a.rational, b.rational) === 0;
  if (a.root && b.root) return sameRoot(a.root, b.root);
  if (a.root || b.root) {
    const [root, other] = a.root ? [a.root, b] : [b.root, a];
    if (other.rational)
      return (
        cmp(root.lower, other.rational) < 0 &&
        cmp(other.rational, root.upper) < 0 &&
        signAt(root.coefficients, other.rational) === 0
      );
    return rootEqualsRadical(root, other.radical);
  }
  return equalValues(
    a.radical ?? rationalValue(a.rational),
    b.radical ?? rationalValue(b.rational),
  );
}

export function withEqualBounds(records) {
  const groups = [];
  const peers = new Map();
  // A local preview may be marked "accepted" before its isolation proof has a receipt.
  for (const record of records) {
    if (record.status !== "framework-verified") continue;
    const value = endpoint(record);
    const group = groups.find((g) => equal(g.value, value));
    if (group) group.members.push(record);
    else groups.push({ value, members: [record] });
  }
  for (const { members } of groups) {
    if (members.length < 2) continue;
    for (const record of members)
      peers.set(
        record.id,
        members
          .filter((r) => r !== record)
          .map(({ id, title }) => ({ id, title })),
      );
  }
  return records.map(({ same_bound_as: ignored, ...r }) =>
    peers.has(r.id) ? { ...r, same_bound_as: peers.get(r.id) } : r,
  );
}
