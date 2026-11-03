import test from "node:test";
import assert from "node:assert/strict";
import legacyDirectories from "../verifier/submission-directories.json" with { type: "json" };
import {
  submissionId,
  submissionDirectories,
  submissionDirectory,
  validateSubmissionDirectory,
  validSubmissionSourcePath,
} from "../verifier/submission-paths.mjs";

test("new dated directories resolve to date-free result IDs", () => {
  const names = ["2026-10-27-example-proof", "2024-02-29-leap-proof"];
  assert.deepEqual(
    submissionDirectories(names),
    new Map([
      ["example-proof", names[0]],
      ["leap-proof", names[1]],
    ]),
  );
  assert.equal(submissionId(names[0]), "example-proof");
  assert.equal(submissionDirectory("example-proof", names), names[0]);
  assert.throws(
    () => submissionDirectory("missing-proof", names),
    /Missing submission directory/,
  );
  assert.equal(validateSubmissionDirectory(names[1]), names[1]);
});

test("new directories require a real calendar date exactly once", () => {
  for (const directory of [
    "example-proof",
    "20261027-example-proof",
    "2026-1-27-example-proof",
    "2026-10-7-example-proof",
    "2026-02-29-example-proof",
    "2026-04-31-example-proof",
    "2026-00-27-example-proof",
    "2026-13-27-example-proof",
    "2026-10-00-example-proof",
    "2026-10-32-example-proof",
    "2026-10-27-Example-proof",
    "2026-10-27-example_proof",
    "2026-10-27-2026-10-27-example-proof",
    "2026-10-27-example-proof-20261027",
    "2026-10-27-example-2026-10-27-proof",
    "2026-10-27-example-20261027-proof",
    "2026-10-27-example-proof/",
    "2026-10-27-example-proof\n",
  ])
    assert.throws(
      () => validateSubmissionDirectory(directory),
      /Invalid submission directory/,
      directory,
    );
  assert.equal(
    submissionId("2026-10-27-example-bound-8746074"),
    "example-bound-8746074",
  );
  assert.equal(
    submissionId("2026-10-27-example-bound-87480870"),
    "example-bound-87480870",
  );
  for (const directory of [undefined, null, 20261027])
    assert.throws(
      () => submissionId(directory),
      /Invalid submission directory/,
    );
});

test("the directory date matches the original PR creation date in UTC", () => {
  const directory = "2026-10-27-example-proof";
  for (const submittedAt of [
    "2026-10-27T00:00:00Z",
    "2026-10-27T23:59:59Z",
    "2026-10-28T00:30:00+02:00",
    "2026-10-26T23:30:00-02:00",
  ])
    assert.equal(
      validateSubmissionDirectory(directory, { submittedAt }),
      directory,
    );
  for (const submittedAt of ["2026-10-26T23:59:59Z"])
    assert.throws(
      () => validateSubmissionDirectory(directory, { submittedAt }),
      /PR submission date/,
    );
  for (const submittedAt of ["", "not-a-timestamp", null])
    assert.throws(
      () => validateSubmissionDirectory(directory, { submittedAt }),
      /Missing valid PR submission date/,
    );
});

test("renamed legacy submissions preserve their stable IDs and historical paths", () => {
  for (const [id, directory] of Object.entries(legacyDirectories)) {
    assert.equal(validateSubmissionDirectory(directory), directory);
    assert.equal(submissionId(directory), id);
    assert.equal(submissionId(id), id);
    assert.ok(validSubmissionSourcePath(`submissions/${directory}/src`, id));
    assert.ok(validSubmissionSourcePath(`submissions/${id}/src`, id));
    assert.throws(
      () => submissionDirectories([id, directory]),
      /Duplicate submission directories/,
    );
  }
  assert.equal(submissionId("2026-10-08-argonaut"), "argonaut-20261008");
  assert.equal(submissionId("2026-10-27-new-argonaut"), "new-argonaut");
  assert.throws(
    () => validateSubmissionDirectory("2026-10-27-openai-baseline"),
    /Use the original submission directory/,
  );
});

test("two directories cannot identify the same submission", () => {
  for (const names of [
    ["2026-10-27-example-proof", "2026-10-28-example-proof"],
    ["example-proof", "2026-10-27-example-proof"],
    ["2026-10-27-example-proof", "2026-10-27-example-proof"],
  ])
    assert.throws(
      () => submissionDirectories(names),
      /Duplicate submission directories/,
    );
});

test("source paths bind the expected ID without accepting traversal or injected suffixes", () => {
  const id = "example-proof";
  assert.ok(
    validSubmissionSourcePath("submissions/2026-10-27-example-proof/src", id),
  );
  assert.ok(validSubmissionSourcePath("submissions/example-proof/src", id));
  for (const path of [
    undefined,
    null,
    "submissions/2026-10-27-other-proof/src",
    "submissions/2026-02-29-example-proof/src",
    "submissions/2026-10-27-example-proof-20261027/src",
    "/submissions/2026-10-27-example-proof/src",
    "submissions//2026-10-27-example-proof/src",
    "submissions/../example-proof/src",
    "submissions/example-proof/../src",
    "submissions/example-proof/src/../src",
    "submissions/example-proof%2fsrc/src",
    "submissions/example-proof\\src",
    "submissions/example-proof/src/",
    "submissions/example-proof/src/Candidate/Main.lean",
    "submissions/example-proof/src\n",
    "submissions/example-proof/src\0",
  ])
    assert.equal(validSubmissionSourcePath(path, id), false, String(path));
});

test("earlier directory dates automatically identify historical imports", () => {
  const directory = "2026-10-08-historical-proof";
  assert.equal(
    validateSubmissionDirectory(directory, {
      submittedAt: "2026-11-03T12:00:00Z",
    }),
    directory,
  );
  assert.equal(
    validateSubmissionDirectory(directory, {
      submittedAt: "2026-10-08T12:00:00Z",
    }),
    directory,
  );
  assert.throws(
    () =>
      validateSubmissionDirectory("2026-11-04-historical-proof", {
        submittedAt: "2026-11-03T12:00:00Z",
      }),
    /cannot be after/,
  );
  assert.throws(
    () =>
      validateSubmissionDirectory("2026-02-30-historical-proof", {
        submittedAt: "2026-11-03T12:00:00Z",
      }),
    /Invalid submission directory/,
  );
});
