import test from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  symlinkSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, dirname } from "node:path";
import { validateMaintainerReplay } from "../core/maintainer-replay.mjs";
const sha = (data) => createHash("sha256").update(data).digest("hex");
const H = "a".repeat(64);
// Synthetic receipt-protocol fixtures only. These do not check any mathematics.
function fixture(t, argonaut = false) {
  const root = mkdtempSync(join(tmpdir(), "qrh-maintainer-replay-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const directory = "public/proofs/replay-fixture";
  const write = (name, data) => {
    const p = join(root, name);
    mkdirSync(dirname(p), { recursive: true });
    writeFileSync(p, data);
  };
  const driverDirectory = `verifier/${argonaut ? "argonaut" : "liu"}`;
  const replayInputs = argonaut
    ? {
        theta_exact: "3499999/4000000",
        pr_head_commit: "d".repeat(40),
        trusted_base_commit: "e".repeat(40),
        release: { tag: "v0.1.8", sha256: H },
      }
    : {};
  const pinsText = JSON.stringify(replayInputs) + "\n";
  write(`${driverDirectory}/replay.py`, "# synthetic trusted driver\n");
  write(`${driverDirectory}/pins.json`, pinsText);
  const contribution = {
    source_commit: "b".repeat(40),
    repository: argonaut
      ? "Argonaut-Math/argonaut-math-quasi-riemann-boundary"
      : "Example/proof",
    ...(argonaut ? { theta: "3499999/4000000" } : {}),
    source_compiler: "4.34.1",
    judge_toolchain: "4.35.0-rc2",
    palomar_commit: "c".repeat(40),
  };
  const report = {
    status: "PASS",
    judge_exit_code: 0,
    source_commit: contribution.source_commit,
    source_repository: `https://github.com/${contribution.repository}`,
    theta_exact: argonaut ? "3499999/4000000" : "(1507 - 2*sqrt(921))/1653",
    ...(argonaut
      ? {
          reviewed_pr_head: replayInputs.pr_head_commit,
          trusted_base_commit: replayInputs.trusted_base_commit,
          release: structuredClone(replayInputs.release),
        }
      : {}),
    source_content_sha256: H,
    driver_sha256: sha("# synthetic trusted driver\n"),
    pins_sha256: sha(pinsText),
    source_compiler: contribution.source_compiler,
    judge_toolchain: contribution.judge_toolchain,
    verifier_commit: contribution.palomar_commit,
    kernels: ["Lean default", "nanoda", "con-ron"],
    allowed_axioms: ["Classical.choice", "Quot.sound", "propext"],
    targets: [
      `QRHBoundsPR${argonaut ? 4 : 3}.allDirichlet`,
      `QRHBoundsPR${argonaut ? 4 : 3}.zeta`,
      `QRHBoundsPR${argonaut ? 4 : 3}.allHecke`,
    ],
    sandbox_preflight: "PASS",
    candidate_mount_preflight: "PASS",
    receipt_outside_candidate: true,
    challenge_exported_before_candidate_execution: true,
    candidate_modules_rebuilt: argonaut ? 152 : 238,
    approved_dependency_modules: 7026,
    extra_official_cache_modules: 4807,
    verified_at: "2026-10-10T09:00:00Z",
  };
  const files = {
    "challenge-src/Challenge.lean": "-- synthetic challenge\n",
    "solution-src/Solution.lean": "-- synthetic wrapper\n",
    "logs/judge.log":
      report.kernels.map((k) => `${k} kernel accepts the solution`).join("\n") +
      "\nYour solution is okay!\n",
    "isolation-controls.json": '{"status":"PASS"}\n',
    "source-manifest.json": "{}\n",
    "tool-pins.json": "{}\n",
    "dependency-pins.json": "{}\n",
    "trusted-library-manifest.json": "{}\n",
  };
  const putJSON = (name, data) => {
    files[name] = JSON.stringify(data) + "\n";
  };
  putJSON("comparator.json", {
    theorem_names: report.targets,
    definition_names: [],
    permitted_axioms: report.allowed_axioms,
    challenge_module: "Challenge",
    solution_module: "Solution",
    external_kernels: {
      nanoda: ["CHECKERS/nanoda_bin"],
      "con-ron": ["CHECKERS/con-ron", "--jobs=2"],
    },
  });
  putJSON("challenge-frozen.json", {
    source_sha256: sha(files["challenge-src/Challenge.lean"]),
    export_sha256: H,
    exported_before_candidate_execution: true,
  });
  const pin = {
    ...(argonaut ? { replay_profile: "argonaut-v0.1.8" } : {}),
    directory,
    theta_exact: report.theta_exact,
    source_content_sha256: H,
    driver_sha256: report.driver_sha256,
    pins_sha256: report.pins_sha256,
    challenge_sha256: sha(files["challenge-src/Challenge.lean"]),
  };
  files["controls/PalomarPreflightSolution.log"] = files["logs/judge.log"];
  files["controls/PalomarPreflightWrong.log"] =
    "Challenge and solution theorem statement do not match\n";
  files["controls/PalomarPreflightIllTyped.log"] =
    "Lean default kernel rejected the solution\n";
  function seal() {
    const artifact_publication = {};
    report.artifacts = {};
    for (const [name, data] of Object.entries(files).filter(
      ([name]) => name !== "result.json" && !name.startsWith("controls/"),
    )) {
      const original =
        name === "isolation-controls.json" ? "preflight-result.json" : name;
      report.artifacts[original] = sha(data);
      artifact_publication[original] = {
        path: name,
        original_sha256: sha(data),
      };
    }
    for (const name of [
      "exports/Challenge.export",
      "exports/Solution.export",
    ]) {
      report.artifacts[name] = H;
      artifact_publication[name] = { path: null, original_sha256: H };
    }
    putJSON("result.json", report);
    putJSON("controls/control-results.json", {
      status: "PASS",
      main_receipt_sha256: sha(files["result.json"]),
      cases: [
        {
          name: "PalomarPreflightSolution",
          exit_code: 0,
          log: "PalomarPreflightSolution.log",
        },
        {
          name: "PalomarPreflightWrong",
          exit_code: 1,
          log: "PalomarPreflightWrong.log",
        },
        {
          name: "PalomarPreflightIllTyped",
          exit_code: 1,
          log: "PalomarPreflightIllTyped.log",
        },
      ],
    });
    const collection = {
      schema_version: 1,
      kind: "independent-maintainer-replay",
      files: Object.fromEntries(
        Object.entries(files).map(([name, data]) => [name, sha(data)]),
      ),
      artifact_publication,
    };
    for (const [name, data] of Object.entries(files))
      write(`${directory}/${name}`, data);
    const bytes = JSON.stringify(collection) + "\n";
    write(`${directory}/collection.json`, bytes);
    pin.receipt_sha256 = sha(files["result.json"]);
    pin.collection_sha256 = sha(bytes);
  }
  seal();
  return {
    root,
    pin,
    report,
    files,
    contribution,
    putJSON,
    write,
    seal,
    validate: () => validateMaintainerReplay(root, pin, contribution),
  };
}

test("Argonaut receipt binds its own runner, release and three target names", (t) => {
  const f = fixture(t, true);
  assert.equal(f.validate().status, "PASS");
  f.report.release.sha256 = "f".repeat(64);
  f.seal();
  assert.throws(f.validate, /Argonaut source release/);
});

test("Argonaut cannot reuse a Liu profile or receipt from another PR revision", (t) => {
  const f = fixture(t, true);
  f.report.reviewed_pr_head = "f".repeat(40);
  f.seal();
  assert.throws(f.validate, /revision/);
  f.pin.replay_profile = "liu-algebraic-v1";
  assert.throws(f.validate);
  f.pin.replay_profile = "arbitrary-candidate-profile";
  assert.throws(f.validate, /unknown replay profile/);
});

test("a later replay preserves the authenticated first success time for the same source", (t) => {
  const f = fixture(t, true);
  const first = structuredClone(f.report);
  first.verified_at = "2026-10-10T08:00:00Z";
  f.putJSON("earlier/result.json", first);
  f.files["earlier/replay.py"] = "# synthetic trusted driver\n";
  f.files["earlier/judge.log"] = f.files["logs/judge.log"];
  f.pin.first_acceptance = {
    receipt: "earlier/result.json",
    driver: "earlier/replay.py",
    log: "earlier/judge.log",
    receipt_sha256: sha(f.files["earlier/result.json"]),
    verified_at: first.verified_at,
  };
  f.seal();
  assert.equal(f.validate().first_verified_at, first.verified_at);
  first.source_commit = "f".repeat(40);
  f.putJSON("earlier/result.json", first);
  f.pin.first_acceptance.receipt_sha256 = sha(f.files["earlier/result.json"]);
  f.seal();
  assert.throws(f.validate, /different source or scope/);
});

test("reviewed maintainer receipt binds exact proof revision, driver and three kernel results", (t) => {
  const f = fixture(t);
  assert.equal(f.validate().status, "PASS");
  f.contribution.source_commit = "d".repeat(40);
  assert.throws(f.validate, /source revision differs/);
});

test("forged collections and changed driver code cannot reuse the acceptance", (t) => {
  const f = fixture(t);
  f.write(`${f.pin.directory}/collection.json`, "{}\n");
  assert.throws(f.validate, /collection differs/);
  f.seal();
  f.write("verifier/liu/replay.py", "# changed driver\n");
  assert.throws(f.validate, /tested driver/);
});

test("receipt cannot omit isolation, early challenge export or outside-candidate provenance", (t) => {
  for (const [key, value] of [
    ["sandbox_preflight", "skipped"],
    ["candidate_mount_preflight", "skipped"],
    ["receipt_outside_candidate", false],
    ["challenge_exported_before_candidate_execution", false],
  ]) {
    const f = fixture(t);
    f.report[key] = value;
    f.seal();
    assert.throws(f.validate, /isolation or challenge ordering/);
  }
});

test("even resealed evidence cannot weaken kernels, axioms, target scope or Comparator definitions", (t) => {
  for (const [key, value] of [
    ["kernels", ["Lean default"]],
    ["allowed_axioms", ["sorryAx"]],
    ["targets", ["QRHBoundsPR3.zeta"]],
  ]) {
    const f = fixture(t);
    f.report[key] = value;
    f.seal();
    assert.throws(f.validate, /scope differs/);
  }
  const f = fixture(t);
  const config = JSON.parse(f.files["comparator.json"]);
  config.definition_names = ["Candidate.fake"];
  f.putJSON("comparator.json", config);
  f.seal();
  assert.throws(f.validate, /Comparator configuration/);
});

test("unlisted evidence, symlinks and unlicensed proof exports fail publication authentication", (t) => {
  const f = fixture(t);
  f.write(`${f.pin.directory}/extra.txt`, "unlisted");
  assert.throws(f.validate, /unlisted/);
  rmSync(join(f.root, f.pin.directory, "extra.txt"));
  symlinkSync("result.json", join(f.root, f.pin.directory, "extra.txt"));
  assert.throws(f.validate, /symlink/);
  rmSync(join(f.root, f.pin.directory, "extra.txt"));
  f.files["proof.export"] = "{}\n";
  f.seal();
  assert.throws(f.validate, /unlicensed source\/export/);
});

test("changed canonical challenge and incomplete kernel logs are rejected", (t) => {
  const f = fixture(t);
  f.files["challenge-src/Challenge.lean"] = "-- changed statement\n";
  f.seal();
  assert.throws(f.validate, /trusted challenge differs/);
  const g = fixture(t);
  g.files["logs/judge.log"] = "Your solution is okay!\n";
  g.seal();
  assert.throws(g.validate, /kernel acceptance logs missing/);
});

test("fresh negative controls cannot be replaced by acceptance logs", (t) => {
  const f = fixture(t);
  f.files["controls/PalomarPreflightWrong.log"] = f.files["logs/judge.log"];
  f.seal();
  assert.throws(f.validate, /statement mismatch control failed/);
  const g = fixture(t);
  g.files["controls/PalomarPreflightIllTyped.log"] = g.files["logs/judge.log"];
  g.seal();
  assert.throws(g.validate, /ill-typed control failed/);
});
