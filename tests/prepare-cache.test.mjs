import test from "node:test";
import assert from "node:assert/strict";
import { mergeContracts } from "../verifier/actions/prepare-cache.mjs";

const contract = (modules) => ({
  build_order: Object.keys(modules),
  module_dependencies: Object.fromEntries(
    Object.entries(modules).map(([m, [, deps]]) => [m, deps]),
  ),
  source_files: Object.fromEntries(
    Object.entries(modules).map(([m, [sha]]) => [
      `src/${m.replaceAll(".", "/")}.lean`,
      sha,
    ]),
  ),
});

test("shared modules of all submissions are merged; private ones are not", () => {
  const base = { "Submissions.base.A": ["a", []] };
  const merged = mergeContracts([
    { contract: contract({ ...base, "Submissions.old.X": ["x", []] }) },
    {
      contract: contract({
        ...base,
        "Candidate.Main": ["c", ["Submissions.base.A"]],
        "Submissions.new.B": ["b", ["Submissions.base.A"]],
        "Submissions.new.C": ["d", ["Candidate.Main"]],
      }),
    },
  ]);
  assert.deepEqual(merged.build_order, [
    "Submissions.base.A",
    "Submissions.old.X",
    "Submissions.new.B",
  ]);
  assert.equal(merged.source_files["src/Submissions/new/B.lean"], "b");
});

test("one module name cannot have two sources", () => {
  assert.throws(
    () =>
      mergeContracts([
        { contract: contract({ "Submissions.s.A": ["1", []] }) },
        { contract: contract({ "Submissions.s.A": ["2", []] }) },
      ]),
    /differs between submissions/,
  );
});
