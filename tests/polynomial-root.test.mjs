import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  algebraicExpression,
  algebraicFromLean,
  exactBound,
  boundTargets,
} from "../core/exact-bound.mjs";
import { parseDeclaration } from "../verifier/pr-admission.mjs";
import { challenge, solutionWrapper } from "../verifier/challenge.mjs";
import { manifest } from "../verifier/manifest.mjs";
import { submissionBound } from "../scripts/submission-catalogue.mjs";

const label = "root([-2,0,1],1/1,2/1)";
const key = `${label} ≤ 3/2`;

test("polynomial roots round trip through declaration, wrapper and catalogue", (t) => {
  const exact = algebraicExpression(label);
  assert.deepEqual(algebraicFromLean(exact.lean), exact);
  assert.deepEqual(algebraicFromLean(exact.lean.replaceAll(" ", "\n")), exact);
  const declaration = parseDeclaration(
    `QRH-Result: root-example\nQRH-Exact: ${label}\nQRH-Bound: 3/2\nQRH-Decimal: 1.5`,
  );
  assert.equal(declaration.theta_exact, key);
  const m = manifest({ id: "root-example", theta_exact: key });
  assert.equal(Object.hasOwn(m, "isolation_lean"), false);
  assert.deepEqual(boundTargets(key), [
    "QRH.canonical_bound",
    "QRH.canonical_bound_le",
    "QRH.canonical_bound_isolated",
  ]);
  assert.match(challenge(m), /theorem canonical_bound_isolated/);
  assert.match(challenge(m), /∃! x : ℝ/);
  const wrapper = solutionWrapper(m);
  assert.match(wrapper, /exact Candidate.bound_isolated/);
  assert.doesNotMatch(wrapper, /sorry/);
  const root = mkdtempSync(join(tmpdir(), "qrh-root-test-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, "Candidate"));
  writeFileSync(
    join(root, "Candidate/Main.lean"),
    `namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (${exact.lean} : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by sorry
theorem bound_le : (${exact.lean} : ℝ) ≤ (3 / 2 : ℝ) := by sorry
theorem bound_isolated : ${exact.isolation_lean} := by sorry
end Candidate`,
  );
  assert.deepEqual(submissionBound(root), exactBound(key));
});

test("reject ambiguous encodings, invalid intervals, oversized inputs and Lean injection", () => {
  for (const value of [
    "root([-2,0,0],1/1,2/1)",
    "root([2,0,-1],1/1,2/1)",
    "root([-4,0,2],1/1,2/1)",
    "root([-2,0,1],2/2,2/1)",
    "root([-2,0,1],2/1,1/1)",
    "root([-2,0,1],1/1,1/1)",
    "root([-02,0,1],1/1,2/1)",
    "root([-0,0,1],1/1,2/1)",
    "root([-2,0,1],1/1,2/1); axiom evil : False",
    `root([${Array(34).fill("1").join(",")}],1/1,2/1)`,
    `root([${"1".repeat(250)},0,1],1/1,2/1)`,
  ])
    assert.throws(() => algebraicExpression(value), undefined, value);
  assert.throws(() =>
    algebraicFromLean("sInf {x | (1 / 1) < x ∧ x < (2 / 1) ∧ (0 + x * 1) = 0}"),
  );
  assert.throws(() =>
    algebraicFromLean(algebraicExpression(label).lean.replace("x *", "x +")),
  );
});

test("isolation is a proof obligation, not a trusted numerical claim", () => {
  // No roots, or two roots: accepted syntax still demands ∃! in Comparator.
  for (const bad of ["root([1,0,1],0/1,2/1)", "root([-1,0,1],-2/1,2/1)"])
    assert.match(
      challenge({ id: "root-example", theta_exact: `${bad} ≤ 3/2` }),
      /∃! x : ℝ/,
    );
  assert.equal(boundTargets("7/8").length, 1);
  assert.equal(boundTargets("(777 − √1081) / 852 ≤ 7/8").length, 2);
});
