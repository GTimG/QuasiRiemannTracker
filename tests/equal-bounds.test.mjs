import assert from "node:assert/strict";
import test from "node:test";
import { withEqualBounds } from "../scripts/equal-bounds.mjs";
import { record } from "./fixtures/catalogue.mjs";

const proof = (id, exact_bound, numerator = "3", denominator = "2") =>
  record({ id, title: id, exact_bound, theta: { numerator, denominator } });
const peers = (r) => r.same_bound_as?.map((p) => p.id) ?? [];

test("different polynomials, multiplicities, ranges and witnesses for the same root", () => {
  const records = [
    proof("quadratic", "root([-2,0,1],1/1,2/1)"),
    proof("extra-factor", "root([-2,-2,1,1],7/5,3/2)", "10", "7"),
    proof("repeated", "root([4,0,-4,0,1],0/1,3/2)"),
    proof("radical", "√8 / 2"),
    proof("other", "root([-3,0,1],1/1,2/1)", "2", "1"),
  ];
  const result = withEqualBounds(records);
  for (const r of result.slice(0, 4))
    assert.deepEqual(
      peers(r),
      records
        .slice(0, 4)
        .filter((p) => p.id !== r.id)
        .map((p) => p.id),
    );
  assert.deepEqual(peers(result[4]), []);
  assert.deepEqual(
    result.map((r) => r.theta),
    records.map((r) => r.theta),
  );
});

test("overlap, touching intervals and roots only at open endpoints do not imply equality", () => {
  for (const [a, b] of [
    ["root([-1,0,1],-2/1,1/2)", "root([-1,0,1],-1/2,2/1)"],
    ["root([-1,0,1],-2/1,0/1)", "root([-1,0,1],0/1,2/1)"],
  ]) {
    for (const r of withEqualBounds([proof("a", a), proof("b", b)]))
      assert.deepEqual(peers(r), []);
  }
  // The common polynomial x^2(x-1)^2 vanishes at both excluded endpoints.
  // Each input has one distinct interior root, 1/3 or 2/3.
  const p = proof("a", "root([0,0,-1,5,-7,3],0/1,1/1)");
  const q = proof("b", "root([0,0,-2,7,-8,3],0/1,1/1)");
  assert.deepEqual(withEqualBounds([p, q]).map(peers), [[], []]);
});

test("rational endpoint equality uses the exact polynomial, never the displayed witness or a float", () => {
  const n = "100000000000000000001",
    d = "200000000000000000000";
  const half = proof("half", undefined, "1", "2"),
    close = proof("close", undefined, n, d);
  const p = proof("root", "root([-1,1,2],0/1,1/1)", "3", "4");
  const q = proof(
    "near-root",
    `root([-${n},99999999999999999999,${d}],0/1,1/1)`,
    "3",
    "4",
  );
  const rationalRadical = proof("simplified", "(√2 * √8) / 8");
  assert.equal(Number(n) / Number(d), 0.5);
  assert.deepEqual(
    withEqualBounds([half, p, rationalRadical, close, q]).map(peers),
    [
      ["root", "simplified"],
      ["half", "simplified"],
      ["half", "root"],
      ["near-root"],
      ["close"],
    ],
  );
});

test("ignore candidate-supplied matches, unverified rows and shared witnesses", () => {
  const p = proof("root", "root([-2,0,1],1/1,2/1)");
  const witness = proof("witness", undefined);
  const pending = {
    ...p,
    id: "pending",
    status: "verification-pending",
    same_bound_as: [{ id: "witness", title: "forged" }],
  };
  const preview = {
    ...p,
    id: "preview",
    status: "accepted",
    first_verified_at: "",
  };
  const input = [p, witness, pending, preview];
  assert.deepEqual(withEqualBounds(input).map(peers), [[], [], [], []]);
  assert.ok(pending.same_bound_as);
});

test("the degree-nine continuum endpoint ties across intervals but differs from its PR #141 witness", () => {
  const coefficients =
    "[-274959111914881,2643837682856883,-11291220876239226,28111661257098222,-44964545308854309,47916748658170215,-34020380857037616,15517896164111592,-4126408710053184,487371101862528]";
  const n =
    "9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717";
  const d =
    "11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700";
  const a = proof("wide", `root(${coefficients},13/15,7/8)`, n, d);
  const b = proof("narrow", `root(${coefficients},8733/10000,4367/5000)`, n, d);
  const rational = proof("witness", undefined, n, d);
  assert.deepEqual(withEqualBounds([a, b, rational]).map(peers), [
    ["narrow"],
    ["wide"],
    [],
  ]);
});

test("an even-multiplicity common root and mixed radicals retain their exact signs", () => {
  const repeated = "root([4,0,-4,0,1],1/1,2/1)";
  const value = "√2 + √3";
  // (sqrt(2) + sqrt(3))^4 - 10(sqrt(2) + sqrt(3))^2 + 1 = 0.
  const records = [
    proof("rep", repeated),
    proof("rep2", "root([4,0,-4,0,1],7/5,3/2)"),
    proof("rad", value, "4", "1"),
    proof("quartic", "root([1,0,-10,0,1],3/1,4/1)", "4", "1"),
    proof("other-conjugate", "root([1,0,-10,0,1],0/1,1/1)"),
  ];
  assert.deepEqual(withEqualBounds(records).map(peers), [
    ["rep2"],
    ["rep"],
    ["quartic"],
    ["rad"],
    [],
  ]);
});
