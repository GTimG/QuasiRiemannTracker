// Authenticate supplied checker evidence. This never executes Lean or a kernel.
import { readFileSync, existsSync, readdirSync, lstatSync } from "node:fs";
import { createHash } from "node:crypto";
import { join } from "node:path";
import { findProofRevision } from "./catalogue-revisions.mjs";

export const NATIVE_ID = "nielstron-algebraic-20261009";
export const KERNEL_DIRECTORY = "public/proofs/nielstron-algebraic-20261009-kernels";
// Frozen before the independent run; installed additively with this validator.
// Binding is supplied explicitly during staging, or read from the reviewed core file.
const THETA = "874957019420098946128603850561452983/1000000000000000000000000000000000000";
const NAMES = [
  "QRHPalomar.allDirichlet",
  "QRHPalomar.zeta",
  "QRHPalomar.allHecke",
  "QRHPalomar.allDirichletExact",
  "QRHPalomar.zetaExact",
  "QRHPalomar.allHeckeExact",
  "QRHPalomar.existsUniqueRoot",
];
const AXIOMS = ["Classical.choice", "Quot.sound", "propext"];
const KERNELS = ["Lean default", "nanoda", "con-ron"];
const PALOMAR = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44";
const TOOLS = {
  lake: "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
  lean: "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
  leanexport:
    "c5bc1a10a21e22cbb3671d65987cdef2076833b14182d823ccb2153adf2fa954",
  leanchecker:
    "9e36e955a251b1313c8eb5b7fa101282d51df109d34d8bb7c1cfdf51985aba29",
  nanoda_bin:
    "8241c5e6baa29490aa118d382f97961b208ae730fdb96545c2abed74c9ece5a8",
  "con-ron": "4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef",
  bwrap: "bb807d18eaee5dad15afd5cf48c8de1c3206ff97e852af693d679d62394eb5a2",
};
const CHECKER_SOURCES = {
  "scripts/verify_submission.py":
    "c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2",
  "scripts/supervise_cgroup.py":
    "3cf9af4fa405e0e2e1bf1e06abe4b53887c1e4a7d5ebe9a6f20b5cf6a66f0e58",
  "scripts/cgroup_delegate.py":
    "c8a44ea58ed9a94db2caf21c66cee3f664c86370fabd50ba56e22fa9d9345824",
};
const DEPENDENCY_PINS = {
  "formalization/.lake/packages/mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
  "upstream/openai-math": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
};
const DEFINITION_PINS = {
  "formalization/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean": "7ef38fb53f462e19dfd6746fc1826423e55bb5e2672c2b5667e2fd4889f401b6",
  "formalization/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean": "8d24b729a30f1fef0820f0f7c9cdbb5910df30dfac2c597eb666794bead08b1c",
  "upstream/openai-math/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean": "9871d175749b34ec40cf66ccc14b4faa0a9ef08831cb3fa901c944e57c7b9ec6",
  "upstream/openai-math/lean/OAI/NumberTheory/DirichletL/Hecke/IdealBridge.lean": "6c1fc33b7372108323bf3af3d4ab6f6e454ea9896b89e78964463a8e35df735f",
};
const digest = (data) => createHash("sha256").update(data).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const mapDigest = (map) => digest(Buffer.from(JSON.stringify(Object.fromEntries(Object.entries(map).sort()))));
const demand = (condition, message) => {
  if (!condition) throw Error(message);
};
const safe = (path) =>
  typeof path === "string" &&
  /^[A-Za-z0-9_./-]+$/.test(path) &&
  !path.startsWith("/") &&
  !path.split("/").some((p) => p === ".." || p === "." || !p);

function inventory(root, relative = "") {
  const result = [];
  for (const name of readdirSync(join(root, relative)).sort()) {
    const path = relative ? relative + "/" + name : name;
    const stat = lstatSync(join(root, path));
    demand(!stat.isSymbolicLink(), "Symlink in independent checker evidence");
    if (stat.isDirectory()) result.push(...inventory(root, path));
    else {
      demand(stat.isFile(), "Non-file in independent checker evidence");
      result.push(path);
    }
  }
  return result.sort();
}

export function validateAlgebraicKernelEvidence(
  root,
  catalogue,
  evidenceDirectory,
  trustedBinding,
) {
  const record = findProofRevision(catalogue, NATIVE_ID);
  if (!record) return null;
  const binding = trustedBinding || JSON.parse(readFileSync(join(root, "core/algebraic-kernel-pins.json")));
  demand(binding.schema_version === 1 && binding.id === NATIVE_ID &&
    binding.theta === THETA && same(binding.declarations, NAMES) &&
    binding.wrappers?.["Challenge.lean"] === "ddc6604d21a5d259dcb9af83398890413cc022f8da0281a86a66178d8cafd338" &&
    /^[a-f0-9]{40}$/.test(binding.source_commit) &&
    [binding.source_manifest_sha256, binding.source_archive_sha256, binding.wrapper_manifest_sha256,
      binding.driver_sha256].every(x => /^[a-f0-9]{64}$/.test(x)) &&
    [binding.source_files,binding.build_modules,binding.qrh_modules].every(x => Number.isSafeInteger(x) && x > 0) &&
    binding.source_files === binding.qrh_modules + 4 &&
    Object.keys(binding.frozen_metadata_sha256 || {}).length === 5,
    "Invalid frozen algebraic source/checker binding");
  const SOURCE_COMMIT = binding.source_commit;
  const SOURCE_MANIFEST = binding.source_manifest_sha256;
  const SOURCE_ARCHIVE = binding.source_archive_sha256;
  demand(mapDigest(binding.wrappers) === binding.wrapper_manifest_sha256,
    "Frozen wrapper manifest digest does not authenticate its files map");
  const directory = evidenceDirectory || join(root, KERNEL_DIRECTORY);
  if (!existsSync(directory)) {
    demand(
      record.status === "verification-pending" && !record.first_verified_at,
      "Native-only result cannot claim independent kernel verification",
    );
    return null;
  }
  demand(lstatSync(directory).isDirectory() && !lstatSync(directory).isSymbolicLink(),
    "Independent evidence directory must be a real directory");
  const bytes = (path) => {
    demand(safe(path), "Unsafe independent evidence path");
    return readFileSync(join(directory, path));
  };
  const json = (path) => JSON.parse(bytes(path));
  const collection = json("collection.json");
  demand(
    collection.schema_version === 1 &&
      collection.kind === "local-mechanical-kernel-evidence" &&
      collection.source_commit === SOURCE_COMMIT,
    "Invalid independent evidence collection",
  );
  demand(
    same(
      inventory(directory),
      [...Object.keys(collection.files), "collection.json"].sort(),
    ),
    "Independent evidence inventory differs from manifest",
  );
  for (const [path, sha] of Object.entries(collection.files))
    demand(
      /^[a-f0-9]{64}$/.test(sha) && digest(bytes(path)) === sha,
      "Independent evidence checksum mismatch: " + path,
    );
  const report = json("result.json");
  demand(
    report.status === "PASS" && report.comparator_exit_code === 0 && report.judge_exit_code === 0,
    "Comparator acceptance is missing",
  );
  demand(report.frozen_build_revalidated_after_judging === true &&
      report.published_source_prefix === `proofs/${NATIVE_ID}/compressed/formalization` &&
      same(report.frozen_metadata_sha256, binding.frozen_metadata_sha256),
    "Frozen source/build metadata were not revalidated after judging");
  demand(
    report.theta === THETA &&
      `${record.theta.numerator}/${record.theta.denominator}` === THETA,
    "Independent checker boundary differs from catalogue",
  );
  demand(
    report.source_commit === SOURCE_COMMIT &&
      report.source_manifest_sha256 === SOURCE_MANIFEST &&
      report.source_archive_sha256 === SOURCE_ARCHIVE &&
      report.wrapper_manifest_sha256 === binding.wrapper_manifest_sha256 &&
      report.published_source_commit === SOURCE_COMMIT &&
      report.signed_admission === false,
    "Independent evidence is not bound to the submitted proof",
  );
  demand(
    report.palomar_commit === PALOMAR &&
      report.palomar_preflight === "passed" &&
      report.statement_definitions_compared === true,
    "Required Comparator/preflight evidence missing",
  );
  demand(
    same(report.declarations, NAMES) &&
      same(report.kernels, KERNELS) &&
      same([...report.allowed_axioms].sort(), AXIOMS),
    "Independent checker target/kernel/axiom scope differs",
  );
  demand(
    report.source_compiler === "4.34.1" &&
      report.judge_toolchain === "4.35.0-rc2",
    "Unexpected checker toolchain",
  );
  demand(
    Number.isFinite(Date.parse(report.verified_at_utc)),
    "Missing real kernel acceptance timestamp",
  );
  const config = json(report.comparator_config);
  demand(
    same(Object.keys(config).sort(), [
      "challenge_module",
      "definition_names",
      "external_kernels",
      "permitted_axioms",
      "solution_module",
      "theorem_names",
    ]) &&
      /^PalomarCanonical[a-f0-9]+\.Challenge$/.test(config.challenge_module) &&
      config.solution_module === "Solution" &&
      same(config.theorem_names, NAMES) &&
      same(config.definition_names, []) &&
      same([...config.permitted_axioms].sort(), AXIOMS) &&
      same(Object.keys(config.external_kernels).sort(), [
        "con-ron",
        "nanoda",
      ]) &&
      config.external_kernels["con-ron"][0].endsWith(
        "/tools/lean-4.35.0-rc2-linux/bin/con-ron",
      ) &&
      same(config.external_kernels["con-ron"].slice(1), ["--jobs=2"]) &&
      config.external_kernels.nanoda[0].endsWith(
        "/tools/lean-4.35.0-rc2-linux/bin/nanoda_bin",
      ) &&
      config.external_kernels.nanoda.length === 1,
    "Comparator configuration weakens the required check",
  );
  const judge = bytes(report.judge_log).toString("utf8");
  demand(
    judge.includes("Your solution is okay!") &&
      KERNELS.every((name) =>
        judge.includes(name + " kernel accepts the solution"),
      ),
    "Judge log does not contain all kernel acceptances",
  );
  const preflight = json(report.preflight_results);
  demand(
    same(
      preflight.cases.map((c) => c.name),
      [
        "PalomarPreflightSolution",
        "PalomarPreflightWrong",
        "PalomarPreflightIllTyped",
      ],
    ),
    "Positive and both negative preflight controls are required",
  );
  const [positive, mismatch, illtyped] = preflight.cases;
  demand(
    positive.exit_code === 0 &&
      Number.isInteger(mismatch.exit_code) &&
      mismatch.exit_code !== 0 &&
      Number.isInteger(illtyped.exit_code) &&
      illtyped.exit_code !== 0,
    "Preflight control exit statuses are invalid",
  );
  const positiveLog = bytes(positive.log).toString("utf8");
  demand(
    positiveLog.includes("Your solution is okay!") &&
      KERNELS.every((name) =>
        positiveLog.includes(name + " kernel accepts the solution"),
      ),
    "Matching preflight proof was not accepted by every kernel",
  );
  demand(
    bytes(mismatch.log)
      .toString("utf8")
      .includes("Challenge and solution theorem statement do not match"),
    "Statement-mismatch control was not rejected by Comparator",
  );
  demand(
    bytes(illtyped.log)
      .toString("utf8")
      .includes("Lean default kernel rejected the solution"),
    "Ill-typed control was not rejected by Lean's kernel",
  );
  const artifacts = report.artifacts;
  for (const [path, sha] of Object.entries(artifacts)) {
    demand(
      safe(path) && /^[a-f0-9]{64}$/.test(sha),
      "Invalid checker artifact digest",
    );
    if (path.startsWith("exports/")) {
      demand(
        Number.isSafeInteger(report.export_sizes[path]) &&
          report.export_sizes[path] > 0,
        "Omitted proof export requires its actual size and digest",
      );
    } else
      demand(
        digest(bytes(path)) === sha,
        "Checker report artifact differs: " + path,
      );
  }
  const originalReport = json("original-report.json");
  const transformations = json("publication-transformations.json");
  const renamed = transformations.path_mapping;
  demand(renamed && typeof renamed === "object" && Array.isArray(transformations.files),
    "Publication transformation receipt is missing");
  const changed = new Map();
  for (const item of transformations.files) {
    demand(safe(item.published_path) && !changed.has(item.published_path) &&
        /^[a-f0-9]{64}$/.test(item.original_sha256) &&
        item.published_sha256 === collection.files[item.published_path] &&
        typeof item.workspace_prefix_neutralized === "boolean",
      "Invalid or unauthenticated publication transformation");
    changed.set(item.published_path, item);
  }
  const publicationFields = new Set(["source_commit", "source_archive_sha256", "comparator_config",
    "judge_log", "challenge_source", "solution_source", "preflight_results", "tool_pins", "runner",
    "signed_admission", "artifacts", "export_sizes", "publication_note"]);
  for (const [key, value] of Object.entries(originalReport))
    if (!publicationFields.has(key)) demand(same(report[key], value),
      "Publication changed an original outcome or scope field: " + key);
  for (const [originalPath, originalDigest] of Object.entries(originalReport.artifacts)) {
    demand(safe(originalPath) && /^[a-f0-9]{64}$/.test(originalDigest),
      "Malformed original checker artifact receipt");
    if (originalPath.startsWith("exports/")) {
      demand(artifacts[originalPath] === originalDigest,
        "Publication changed an original proof export digest");
    } else {
      const publishedPath = renamed[originalPath] || originalPath;
      const transformation = changed.get(publishedPath);
      demand(safe(publishedPath) && transformation?.original_sha256 === originalDigest &&
          transformation.published_sha256 === artifacts[publishedPath],
        "Original checker artifact is not linked to authenticated published bytes");
    }
  }
  demand(changed.get("original-report.json")?.published_sha256 === collection.files["original-report.json"],
    "Original run report lacks an explicit publication digest relation");
  const reconstructedControls = structuredClone(preflight);
  const reverseNames = new Map(Object.entries(renamed).map(([before, after]) => [after, before]));
  for (const item of reconstructedControls.cases) {
    demand(reverseNames.has(item.log), "Control log path lacks a recorded rename");
    item.log = reverseNames.get(item.log);
  }
  demand(digest(Buffer.from(JSON.stringify(reconstructedControls, null, 2) + "\n")) ===
      originalReport.artifacts[originalReport.preflight_results],
    "Published controls changed more than their declared log filenames");
  for (const path of [
    report.challenge_source,
    report.solution_source,
    report.comparator_config,
    report.judge_log,
    report.preflight_results,
    report.tool_pins,
    report.runner,
  ])
    demand(
      artifacts[path] === collection.files[path],
      "Required checker artifact is not authenticated: " + path,
    );
  const pins = json(report.tool_pins);
  const inputPins = json("checker-binary-pins.json");
  demand(
    pins.palomar_commit === PALOMAR &&
      pins.exporter_commit === "076e8e57707e813375e8f9da8bf989799ace9680" &&
      Object.entries(TOOLS).every(
        ([name, sha]) => pins.judge_tools[name] === sha,
      ) &&
      pins.source_exporter_sha256 ===
        "8c5d64ba68f4d3a68b3bcb7e1c5f188e35ae573b29470b8d4530a62324c9ddd1" &&
      pins.source_lean_sha256 ===
        "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550" &&
      pins.verifier_script_sha256 ===
        "c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2" &&
      pins.driver_sha256 === collection.files[report.runner] &&
      pins.driver_sha256 === binding.driver_sha256,
    "Checker binaries, source pins or runner changed",
  );
  demand(
    Object.entries(TOOLS)
      .filter(([name]) => name !== "bwrap")
      .every(([name, sha]) => inputPins[name]?.sha256 === sha) &&
      inputPins.exporter?.sha256 === pins.source_exporter_sha256 &&
      inputPins.exporter?.source_commit === pins.exporter_commit,
    "Flat checker input pins differ from the accepted run",
  );
  const inputs = json("source-inputs.json"),
    build = json("build-inputs.json");
  demand(
    inputs.manifest_sha256 === SOURCE_MANIFEST &&
      build.status === "PASS" &&
      build.modules_checked === binding.build_modules &&
      build.qrh_modules_checked === binding.qrh_modules &&
      build.sources_and_oleans_rehashed === true &&
      build.challenge_imports_no_QRH === true &&
      build.lean_path_artifacts_matched === true &&
      build.published_source_binding?.commit === SOURCE_COMMIT &&
      build.published_source_binding?.prefix === `proofs/${NATIVE_ID}/compressed/formalization` &&
      build.published_source_binding?.manifest_files_matched_to_git_blobs === binding.source_files &&
      build.definition_provenance?.tracked_worktrees_clean === true &&
      build.definition_provenance?.git_blobs_matched === true &&
      same(build.definition_provenance?.repositories, DEPENDENCY_PINS) &&
      same(build.definition_provenance?.protected_definition_files, DEFINITION_PINS),
    "Checker input integrity audit is incomplete",
  );
  const accepted = build.accepted_challenge_inventory;
  demand(accepted?.baseline_run === "candidate-n24-r2" &&
      accepted.build_inputs_sha256 === "38cef2b708ec35bf5a5192addbc87ce9529c3e44ca0886123027e1732f9d6809" &&
      accepted.source_graph_sha256 === "7364b78eb62004edfe9d7c3ebacd0b4f8cbc65f53e07dd6200816a92338cca7e" &&
      accepted.build_records_sha256 === "530332d9c117d87456183de122ac4fc685661f0d7aa671253d91d31bd9018b00" &&
      accepted.module_count === 4386 &&
      accepted.source_inventory_sha256 === "5456479c52d33818cfe34e8aee9700bca6e433677c28b3255d6cfb1465734e22" &&
      accepted.olean_inventory_sha256 === "195699da003491e53896190deed2c9c989324a66c4f6ffd61a81613e078ee3c6" &&
      accepted.every_source_and_artifact_matches === true,
    "Shared independent Challenge imports are not bound to accepted source/artifact inventories");
  const challengeAudit = json("challenge-source-audit.json"),
    checkerAudit = json("checker-source-audit.json");
  demand(
    challengeAudit.status === "PASS" &&
      challengeAudit.source_hashes_checked === 4386 &&
      challengeAudit.olean_hashes_checked === 4386 &&
      same(challengeAudit.QRH_modules_in_challenge_closure, []) &&
      challengeAudit.source_hashes_match_recorded_build_graph === true &&
      challengeAudit.olean_hashes_match_recorded_build_records === true &&
      challengeAudit.protected_definition_files.length === 4 &&
      challengeAudit.protected_definition_files.every(
        (p) => p.matches_pinned_git_blob === true,
      ),
    "Independent mathematical definitions are not bound to pinned sources",
  );
  demand(
    checkerAudit.status === "PASS" &&
      checkerAudit.palomar_commit === PALOMAR &&
      checkerAudit.checker_code_modified === false &&
      Object.keys(checkerAudit.verifier_and_supervisors).length === 3 &&
      Object.entries(CHECKER_SOURCES).every(
        ([name, sha]) =>
          checkerAudit.verifier_and_supervisors[name]?.sha256 === sha &&
          checkerAudit.verifier_and_supervisors[name]
            ?.matches_pinned_git_blob === true,
      ),
    "Checker implementation integrity evidence missing",
  );
  const provisioning = json("namespace-provisioning.json"),
    cleanup = json("namespace-cleanup.json");
  demand(
    provisioning.status === "temporary_profile_active" &&
      provisioning.record_kind === "Read-only observation during the algebraic run, before cleanup" &&
      provisioning.profile_loaded === true &&
      provisioning.global_userns_restriction_current === "1" &&
      Number.isFinite(Date.parse(provisioning.recorded_at_utc)) &&
      Number.isFinite(Date.parse(report.started_utc)) &&
      Date.parse(report.started_utc) <= Date.parse(provisioning.recorded_at_utc) &&
      Date.parse(provisioning.recorded_at_utc) <= Date.parse(report.verified_at_utc) &&
      Number.isSafeInteger(provisioning.proof_execution_uid) && provisioning.proof_execution_uid > 0 &&
      provisioning.binary_sha256 === TOOLS.bwrap &&
      provisioning.binary_owner_uid === 0 &&
      provisioning.proof_execution_as_root === false &&
      provisioning.global_userns_restriction_changed === false &&
      provisioning.persistent_configuration_created === false &&
      report.host_policy_changed === true &&
      report.global_userns_restriction_unchanged === true &&
      provisioning.profile_sha256 ===
        digest(bytes("temporary-apparmor-profile.txt")) &&
      pins.temporary_apparmor_profile_sha256 === provisioning.profile_sha256,
    "Temporary sandbox provisioning evidence does not match the checked run",
  );
  demand(
    cleanup.status === "temporary_profile_and_binary_removed" &&
      cleanup.profile_loaded === false &&
      cleanup.temporary_directory_exists === false &&
      cleanup.global_userns_restriction === "1",
    "Temporary sandbox cleanup has not completed",
  );
  demand(
    same(Object.keys(report.export_sizes).sort(), ["exports/challenge.export", "exports/solution.export"]) &&
      same(Object.keys(artifacts).filter(path => path.startsWith("exports/")).sort(),
        ["exports/challenge.export", "exports/solution.export"]) &&
      ["challenge", "solution"].every(name =>
        report.exports?.[name]?.sha256 === artifacts[`exports/${name}.export`] &&
        report.exports?.[name]?.bytes === report.export_sizes[`exports/${name}.export`]),
    "Both independently exported proof artifacts are required",
  );
  const canonicalChallenge = readFileSync(join(root, `proofs/${NATIVE_ID}/verification/src/Challenge.lean`));
  const canonicalSolution = readFileSync(join(root, `proofs/${NATIVE_ID}/verification/src/Solution.lean`));
  demand(bytes(report.challenge_source).equals(canonicalChallenge) &&
      bytes(report.solution_source).equals(canonicalSolution) &&
      digest(canonicalChallenge) === binding.wrappers["Challenge.lean"] &&
      digest(canonicalSolution) === binding.wrappers["Solution.lean"],
    "Seven-target wrappers differ from the independently frozen published statements");
  demand(same(report.reference_templates, binding.wrappers),
    "Actual checked wrapper inputs differ from frozen source hashes");
  const replay = JSON.parse(
    readFileSync(
      join(root, `proofs/${NATIVE_ID}/source-inputs.json`),
    ),
  );
  demand(Object.keys(replay.files).length === binding.source_files,
    "Frozen algebraic source inventory count changed");
  demand(
    replay.manifest_sha256 === SOURCE_MANIFEST &&
      mapDigest(replay.files) === SOURCE_MANIFEST && mapDigest(inputs.files) === SOURCE_MANIFEST,
    "Submitted source manifest changed",
  );
  demand(
    same(
      Object.entries(inputs.files).sort(),
      Object.entries(replay.files).sort(),
    ),
    "Actual checker source inventory differs from submitted proof",
  );
  for (const [path, sha] of Object.entries(replay.files))
    demand(
      safe(path) &&
        digest(
          readFileSync(
            join(root, `proofs/${NATIVE_ID}/compressed/formalization`, path),
          ),
        ) === sha,
      "Checker source differs from immutable submission",
    );
  demand(
    digest(
      readFileSync(
        join(root, `public/proofs/${NATIVE_ID}/source-public.tar.gz`),
      ),
    ) === SOURCE_ARCHIVE,
    "Reviewed published native source archive changed",
  );
  if (record.status === "framework-verified") {
    demand(
      record.first_verified_at === report.verified_at_utc &&
        record.source_commit === SOURCE_COMMIT,
      "Catalogue date/source must identify this genuine checker acceptance",
    );
  } else
    demand(
      record.status === "verification-pending" && !record.first_verified_at,
      "Unsupported native contribution verification status",
    );
  return report;
}
