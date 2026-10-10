import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  readFileSync,
  writeFileSync,
  rmSync,
  symlinkSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, dirname } from "node:path";
import { createHash } from "node:crypto";
import { validateExternalKernelEvidence } from "../core/external-kernel-evidence.mjs";

const digest = (value) => createHash("sha256").update(value).digest("hex");
const H = "a".repeat(64),
  COMMIT = "b".repeat(40);
const targets = [
  "QRHPalomar.allDirichlet",
  "QRHPalomar.zeta",
  "QRHPalomar.allHecke",
];
const axioms = ["Classical.choice", "Quot.sound", "propext"];
const kernels = ["Lean default", "nanoda", "con-ron"];
const accepted = `${kernels.map((name) => `${name} kernel accepts the solution`).join("\n")}\nYour solution is okay!\n`;

test("Argonaut cannot promote submitted logs without an isolated maintainer receipt", () => {
  const catalogue = {
    records: [{ id: "argonaut-20261008", status: "framework-verified" }],
  };
  assert.throws(
    () =>
      validateExternalKernelEvidence("/unused", catalogue, {
        schema_version: 1,
        entries: { "argonaut-20261008": { directory: "public/proofs/old" } },
      }),
    /isolated maintainer replay/,
  );
});

// Synthetic protocol fixtures test authentication failures, not mathematics.
function fixture(t, mode = "archived-source", algebraic = false) {
  const root = mkdtempSync(join(tmpdir(), "qrh-external-evidence-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const directory = "public/proofs/test-external-kernels";
  const record = {
    id: "test-external",
    repository: "Example/proof",
    source_commit: COMMIT,
    theta: { numerator: "7", denominator: "8" },
    entrypoint: {
      module: "Candidate.Main",
      declaration: "Candidate.allDirichlet",
    },
    status: "framework-verified",
    first_verified_at: "2026-10-10T10:00:00Z",
  };
  if (algebraic) record.exact_bound = "(1507 − 2√921) / 1653";
  const external = {
    "con-ron": ["/opt/checker/con-ron", "--jobs=2"],
    nanoda: ["/opt/checker/nanoda_bin"],
  };
  const config = {
    challenge_module: "Canonical.Challenge",
    solution_module: "Solution",
    definition_names: [],
    theorem_names: targets,
    permitted_axioms: axioms,
    external_kernels: external,
  };
  const files = {
    "src/Challenge.lean": "-- synthetic exact challenge\n",
    "src/Solution.lean": "-- synthetic original wrapper\n",
    "judge.log": accepted,
    "controls/matching.log": accepted,
    "controls/mismatched.log":
      "Challenge and solution theorem statement do not match\n",
    "controls/ill-typed.log": "Lean default kernel rejected the solution\n",
    "verify.py": "# synthetic original runner\n",
    "reproduce.py": "# fetch fixed source and re-run checks\n",
  };
  const putJSON = (path, object) => {
    files[path] = `${JSON.stringify(object, null, 2)}\n`;
  };
  putJSON("comparator.json", config);
  putJSON("controls.json", {
    cases: [
      {
        name: "PalomarPreflightSolution",
        exit_code: 0,
        log: "controls/matching.log",
      },
      {
        name: "PalomarPreflightWrong",
        exit_code: 1,
        log: "controls/mismatched.log",
      },
      {
        name: "PalomarPreflightIllTyped",
        exit_code: 1,
        log: "controls/ill-typed.log",
      },
    ],
  });
  putJSON("source-inputs.json", {
    manifest_sha256: H,
    files: { "Candidate/Main.lean": H },
  });
  putJSON("native-build.json", {
    status: "PASS",
    sources_and_oleans_rehashed: true,
    challenge_imports_no_candidate: true,
    source_manifest_sha256: H,
  });
  putJSON("source-provenance.json", {
    repository: record.repository,
    source_commit: COMMIT,
    publication_mode: mode,
    ...(mode === "archived-source" ? { license_file: "LICENSE.txt" } : {}),
  });
  putJSON("tools.json", {
    palomar_commit: COMMIT,
    exporter_commit: COMMIT,
    source_lean_sha256: H,
    source_exporter_sha256: H,
    driver_sha256: digest(files["verify.py"]),
    judge_tools: Object.fromEntries(
      [
        "lean",
        "lake",
        "leanexport",
        "leanchecker",
        "nanoda_bin",
        "con-ron",
      ].map((name) => [name, H]),
    ),
  });
  if (mode === "archived-source") {
    files["source-public.tar.gz"] =
      "synthetic archive bytes; contents reviewed separately\n";
    files["LICENSE.txt"] = "Synthetic licensed fixture\n";
  }
  const report = {
    status: "PASS",
    comparator_exit_code: 0,
    judge_exit_code: 0,
    kernels,
    declarations: targets,
    allowed_axioms: axioms,
    palomar_preflight: "passed",
    statement_definitions_compared: true,
    theta: "7/8",
    ...(algebraic ? { theta_exact: record.exact_bound } : {}),
    verified_at_utc: record.first_verified_at,
    source_commit: COMMIT,
    source_manifest_sha256: H,
    source_compiler: "4.34.1",
    judge_toolchain: "4.35.0-rc2",
    palomar_commit: COMMIT,
    challenge_source: "src/Challenge.lean",
    solution_source: "src/Solution.lean",
    comparator_config: "comparator.json",
    judge_log: "judge.log",
    preflight_results: "controls.json",
    tool_pins: "tools.json",
    runner: "verify.py",
    source_inputs: "source-inputs.json",
    native_build_report: "native-build.json",
    source_provenance: "source-provenance.json",
    reproduction_script: "reproduce.py",
    export_sizes: {
      "exports/challenge.export": 10,
      "exports/solution.export": 20,
    },
    ...(mode === "archived-source"
      ? {
          source_archive: "source-public.tar.gz",
          source_archive_sha256: digest(files["source-public.tar.gz"]),
        }
      : {}),
  };
  const pin = {
    directory,
    repository: record.repository,
    source_commit: COMMIT,
    theta: "7/8",
    ...(algebraic ? { theta_exact: record.exact_bound } : {}),
    entrypoint: structuredClone(record.entrypoint),
    source_manifest_sha256: H,
    source_compiler: report.source_compiler,
    judge_toolchain: report.judge_toolchain,
    palomar_commit: COMMIT,
    challenge_sha256: digest(files[report.challenge_source]),
    challenge_module: config.challenge_module,
    solution_module: config.solution_module,
    external_kernels: structuredClone(external),
    publication_mode: mode,
  };
  const reviewed = { schema_version: 1, entries: { [record.id]: pin } };
  const seal = () => {
    report.artifacts = Object.fromEntries(
      Object.entries(files)
        .filter(([path]) => path !== "result.json")
        .map(([path, contents]) => [path, digest(contents)]),
    );
    for (const path of Object.keys(report.export_sizes))
      report.artifacts[path] = H;
    putJSON("result.json", report);
    const collection = `${JSON.stringify({ schema_version: 1, kind: "local-mechanical-kernel-evidence", files: Object.fromEntries(Object.entries(files).map(([path, contents]) => [path, digest(contents)])) }, null, 2)}\n`;
    for (const [path, contents] of [
      ...Object.entries(files),
      ["collection.json", collection],
    ]) {
      mkdirSync(dirname(join(root, directory, path)), { recursive: true });
      writeFileSync(join(root, directory, path), contents);
    }
    pin.collection_sha256 = digest(collection);
  };
  seal();
  return {
    root,
    directory,
    record,
    report,
    pin,
    files,
    putJSON,
    seal,
    validate: () =>
      validateExternalKernelEvidence(root, { records: [record] }, reviewed),
  };
}

test("pending external entries cannot self-upgrade without reviewed pins", () => {
  const record = {
    id: "external",
    status: "verification-pending",
    first_verified_at: "",
  };
  const run = () =>
    validateExternalKernelEvidence(
      "unused",
      { records: [record] },
      { schema_version: 1, entries: { external: null } },
    );
  assert.deepEqual(run(), []);
  record.status = "framework-verified";
  assert.throws(run, /no reviewed independent acceptance/);
  record.status = "verification-pending";
  record.first_verified_at = "2026-10-10T10:00:00Z";
  assert.throws(run, /no reviewed independent acceptance/);
});

for (const mode of ["archived-source", "remote-source"])
  test(`${mode} authenticates all kernels and exact source bindings`, (t) => {
    const f = fixture(t, mode, mode === "remote-source");
    assert.equal(f.validate()[0].status, "PASS");
    f.record.first_verified_at = "2026-10-09T10:00:00Z";
    assert.throws(f.validate, /status\/date/);
    f.record.first_verified_at = f.report.verified_at_utc;
    f.record.source_commit = "c".repeat(40);
    assert.throws(f.validate, /source revision/);
  });

test("a changed file or self-rewritten collection cannot reuse reviewed acceptance", (t) => {
  const f = fixture(t);
  writeFileSync(join(f.root, f.directory, "judge.log"), "different\n");
  assert.throws(f.validate, /checksum mismatch/);
  const collection = join(f.root, f.directory, "collection.json");
  writeFileSync(collection, `${readFileSync(collection, "utf8")}\n`);
  assert.throws(f.validate, /collection differs/);
});

test("unlisted evidence and symlinks are rejected", (t) => {
  const f = fixture(t);
  const extra = join(f.root, f.directory, "extra.txt");
  writeFileSync(extra, "extra");
  assert.throws(f.validate, /inventory differs/);
  rmSync(extra);
  symlinkSync("judge.log", extra);
  assert.throws(f.validate, /symlink/);
});

test("even a newly pinned package cannot weaken kernel, axiom or definition scope", (t) => {
  const f = fixture(t);
  f.report.kernels = ["Lean default"];
  f.seal();
  assert.throws(f.validate, /kernel, target or axiom/);
  f.report.kernels = kernels;
  f.report.allowed_axioms = [...axioms, "sorryAx"];
  f.seal();
  assert.throws(f.validate, /kernel, target or axiom/);
  f.report.allowed_axioms = axioms;
  f.report.statement_definitions_compared = false;
  f.seal();
  assert.throws(f.validate, /statement\/definition/);
});

test("canonical challenge, Comparator options and negative controls remain compulsory", (t) => {
  const f = fixture(t);
  f.files[f.report.challenge_source] += "-- weakened\n";
  f.seal();
  assert.throws(f.validate, /canonical independent challenge/);
  f.pin.challenge_sha256 = digest(f.files[f.report.challenge_source]);
  const config = JSON.parse(f.files["comparator.json"]);
  config.definition_names = ["Candidate.fakeLFunction"];
  f.putJSON("comparator.json", config);
  f.seal();
  assert.throws(f.validate, /configuration weakens/);
  config.definition_names = [];
  f.putJSON("comparator.json", config);
  f.files["controls/mismatched.log"] = accepted;
  f.seal();
  assert.throws(f.validate, /statement mismatch/);
});

test("native source integrity and independently defined challenge are required", (t) => {
  const f = fixture(t);
  const native = JSON.parse(f.files["native-build.json"]);
  native.challenge_imports_no_candidate = false;
  f.putJSON("native-build.json", native);
  f.seal();
  assert.throws(f.validate, /source\/build integrity/);
  native.challenge_imports_no_candidate = true;
  native.sources_and_oleans_rehashed = false;
  f.putJSON("native-build.json", native);
  f.seal();
  assert.throws(f.validate, /source\/build integrity/);
});

test("the algebraic theorem cannot be replaced by its plotted endpoint", (t) => {
  const f = fixture(t, "remote-source", true);
  delete f.report.theta_exact;
  f.seal();
  assert.throws(f.validate, /exact algebraic target/);
});

test("remote-only publication excludes candidate source and proof exports", (t) => {
  const f = fixture(t, "remote-source", true);
  f.files["src/Candidate.lean"] = "-- third-party source\n";
  f.seal();
  assert.throws(f.validate, /only original challenge\/wrapper/);
  delete f.files["src/Candidate.lean"];
  rmSync(join(f.root, f.directory, "src/Candidate.lean"));
  f.files["proof.ndjson"] = "{}\n";
  f.seal();
  assert.throws(f.validate, /must not redistribute/);
});
