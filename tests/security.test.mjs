import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  cpSync,
  writeFileSync,
  symlinkSync,
  rmSync,
  readFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { manifest, submission, safePath } from "../verifier/manifest.mjs";
import {
  challenge,
  solutionWrapper,
  comparatorConfig,
} from "../verifier/challenge.mjs";
import { readJSON, envelope, sha256 } from "../verifier/common.mjs";
import { receipt, reviewed } from "../verifier/receipts.mjs";
import { generateRegistry } from "../verifier/registry.mjs";
import { classify, workerArgs, preflight } from "../verifier/runner.mjs";
import { allowedChanges } from "../verifier/github.mjs";
import { setup } from "./helpers.mjs";
const valid = () => readJSON("submissions/openai-baseline/manifest.json");
test("challenge fixes quantifiers, pole exclusion and definitions; only literals vary", () => {
  const m = valid();
  m.theta = { numerator: "3", denominator: "4" };
  const c = challenge(m);
  assert.match(
    c,
    /\{q : ℕ\} \[NeZero q\] \(χ : DirichletCharacter ℂ q\) \{s : ℂ\}/,
  );
  assert.match(
    c,
    /\(hs : \(3 \/ 4 : ℝ\) < s.re\) \(hpole : ¬ \(χ = 1 ∧ s = 1\)\)/,
  );
  assert.match(c, /_root_.DirichletCharacter.LFunction χ s ≠ 0/);
  assert.match(c, /sorry/);
  assert.doesNotMatch(solutionWrapper(m), /sorry/);
  const config = comparatorConfig();
  assert.deepEqual(config.definition_names, []);
  assert.deepEqual([...config.permitted_axioms].sort(), [
    "Classical.choice",
    "Quot.sound",
    "propext",
  ]);
  assert.ok(config.external_kernels.nanoda);
});
test("manifest forbids candidate-defined challenge/verified claims and metadata injection", () => {
  for (const change of [
    { verified: true },
    { predicate: "True" },
    { theta: { numerator: "14", denominator: "16" } },
    { title: "<img onerror=alert(1)>" },
    { references: [{ label: "bad", url: "javascript:alert(1)" }] },
    {
      entrypoint: {
        module: "Candidate.Main\naxiom hack : False",
        declaration: "hack",
      },
    },
    { builds_on: ["openai-baseline"] },
  ])
    assert.throws(() => manifest({ ...valid(), ...change }));
});
test("unsafe paths, symlinks and submitted caches are rejected; source changes alter digest", () => {
  for (const p of [
    "../escape",
    "a/../../b",
    "/tmp/a",
    "a\\b",
    "a//b",
    "a/./b",
    "a\u0000b",
  ])
    assert.throws(() => safePath(p));
  const dir = mkdtempSync(path.join(tmpdir(), "qrh-test-"));
  try {
    cpSync("submissions/openai-baseline", dir, { recursive: true });
    const before = submission(dir);
    writeFileSync(
      path.join(dir, "src/Candidate/Main.lean"),
      "-- changed\n" +
        readFileSync(path.join(dir, "src/Candidate/Main.lean"), "utf8"),
    );
    assert.notEqual(submission(dir).content_digest, before.content_digest);
    mkdirSync(path.join(dir, ".lake"));
    assert.throws(() => submission(dir));
    rmSync(path.join(dir, ".lake"), { recursive: true });
    symlinkSync("/etc/passwd", path.join(dir, "src/Candidate/Evil.lean"));
    assert.throws(() => submission(dir));
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
test("forged, stale, cross-repo, altered-bound and partial receipts fail closed", () => {
  const t = setup();
  assert.equal(receipt(t.receipt, t.policy).status, "accepted");
  assert.throws(() => receipt({ ...t.receipt, signature: "forged" }, t.policy));
  assert.throws(() =>
    receipt(t.receipt, t.policy, {
      ...t.payload,
      source_commit: "e".repeat(40),
    }),
  );
  assert.throws(() =>
    receipt(t.receipt, t.policy, {
      ...t.payload,
      content_digest: "f".repeat(64),
    }),
  );
  for (const change of [
    { status: "checking-failed" },
    { repository: "attacker/fork" },
    { pin_digest: "a".repeat(64) },
    { challenge_sha256: "a".repeat(64) },
    {
      results: {
        comparator: "accepted",
        nanoda: "not-run",
        isolation: "passed",
      },
    },
    {
      manifest: {
        ...t.payload.manifest,
        theta: { numerator: "3", denominator: "4" },
      },
    },
  ])
    assert.throws(() =>
      receipt(
        envelope({ ...t.payload, ...change }, t.vk.privateKey, "v"),
        t.policy,
      ),
    );
});
test("PR cannot approve itself, retain dismissed approval, or use approval for an older head", () => {
  const t = setup();
  const p = {
    base_repository: t.policy.repository,
    author: "reviewer",
    head_sha: t.payload.source_commit,
    merged_at: "2026-10-01",
    merge_commit: "a".repeat(40),
    is_draft: false,
  };
  const approval = {
    id: 1,
    login: "reviewer",
    state: "APPROVED",
    commit_id: p.head_sha,
    submitted_at: "2026-10-01",
  };
  assert.throws(() => reviewed(p, [approval], t.policy));
  p.author = "author";
  assert.equal(reviewed(p, [approval], t.policy).length, 1);
  assert.throws(() =>
    reviewed(
      p,
      [
        approval,
        { ...approval, state: "DISMISSED", submitted_at: "2026-10-02" },
      ],
      t.policy,
    ),
  );
  assert.throws(() =>
    reviewed({ ...p, head_sha: "e".repeat(40) }, [approval], t.policy),
  );
  assert.throws(() =>
    reviewed({ ...p, merged_at: null }, [approval], t.policy),
  );
});
test("registry authenticates records/logs, rejects duplicate IDs and unknown predecessors", () => {
  const t = setup();
  assert.equal(
    generateRegistry([t.bundle], [], t.policy, [t.receipt]).records.length,
    1,
  );
  assert.throws(() =>
    generateRegistry([{ ...t.bundle, log: "forged" }], [], t.policy, [
      t.receipt,
    ]),
  );
  assert.throws(() =>
    generateRegistry([t.bundle, t.bundle], [], t.policy, [t.receipt]),
  );
  assert.throws(() =>
    generateRegistry(
      [
        {
          ...t.bundle,
          publication: envelope(
            { ...t.publicationPayload, source_commit: "f".repeat(40) },
            t.pk.privateKey,
            "p",
          ),
        },
      ],
      [],
      t.policy,
      [t.receipt],
    ),
  );
  const ev = envelope(
    {
      kind: "qrh-event-v1",
      type: "withdraw",
      id: "openai-baseline",
      reason: "Audit finding",
      at: "2026-10-03",
      reviewer: "reviewer",
      previous: null,
    },
    t.pk.privateKey,
    "p",
  );
  const reg = generateRegistry([t.bundle], [ev], t.policy, [t.receipt]);
  assert.equal(reg.records.length, 1);
  assert.equal(reg.active_ids.length, 0);
  assert.throws(() =>
    generateRegistry([t.bundle], [ev, ev], t.policy, [t.receipt]),
  );
});
test("submission PR cannot replace CI, verifier, tools or trusted registry", () => {
  assert.equal(
    allowedChanges([
      {
        filename: "submissions/new-proof/src/Candidate/Main.lean",
        status: "added",
      },
    ]),
    "new-proof",
  );
  for (const file of [
    ".github/workflows/verify-submission.yml",
    "verifier/challenge.mjs",
    "submissions/new-proof/lakefile.lean",
    "submissions/new-proof/.lake/evil.olean",
    "registry/records/fake/receipt.json",
  ])
    assert.throws(() => allowedChanges([{ filename: file, status: "added" }]));
  assert.throws(() =>
    allowedChanges([
      { filename: "submissions/new-proof/manifest.json", status: "renamed" },
    ]),
  );
});
test("worker invocation is immutable, offline, unprivileged and has no shared writable cache", () => {
  const args = workerArgs("sha256:" + "a".repeat(64), "/tmp/test", "test");
  for (const s of [
    "--network=none",
    "--read-only",
    "--user=65532:65532",
    "--cap-drop=ALL",
    "--security-opt=no-new-privileges",
    "--pids-limit=256",
    "--pull=never",
  ])
    assert.ok(args.includes(s));
  assert.equal(args.filter((x) => x === "--mount").length, 1);
  assert.ok(args.includes("type=bind,source=/tmp/test,target=/input,readonly"));
  assert.ok(!args.join(" ").includes("docker.sock"));
  assert.throws(() => workerArgs("worker:latest", "/tmp/test", "test"));
  const script = readFileSync("worker/entrypoint.py", "utf8");
  assert.match(script, /os.execve/);
  assert.doesNotMatch(script, /fake-landrun/);
  assert.ok(
    JSON.parse(readFileSync("worker/seccomp.json")).syscalls[0].names.includes(
      "socketpair",
    ),
  );
});
test("checker infrastructure failure is not labelled mathematical rejection", () => {
  assert.equal(classify(0, null, false, false), "accepted");
  assert.equal(classify(1, null, false, false), "checking-failed");
  assert.equal(classify(139, null, false, false), "checker-crash");
  assert.equal(classify(null, "SIGKILL", true, false), "timed-out");
  assert.equal(classify(null, "SIGKILL", false, true), "resource-exhausted");
});
test("workflows use protected dispatch, exact orchestration commits and pinned actions", () => {
  const v = readFileSync(".github/workflows/verify-submission.yml", "utf8");
  assert.match(v, /workflow_dispatch/);
  assert.doesNotMatch(v, /pull_request_target|secrets\.[^Q]/);
  assert.match(v, /ref: \$\{\{ github.workflow_sha \}\}/);
  assert.match(v, /persist-credentials: false/);
  assert.match(v, /needs: check/);
  for (const f of ["verify-submission.yml", "publish-record.yml", "ci.yml"])
    for (const line of readFileSync(".github/workflows/" + f, "utf8")
      .split("\n")
      .filter((l) => l.includes("uses:")))
      assert.match(line, /@[a-f0-9]{40}(?:\s|$)/);
});
