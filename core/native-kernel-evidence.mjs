// Authenticate supplied checker evidence. This never executes Lean or a kernel.
import { readFileSync, existsSync, readdirSync, lstatSync } from "node:fs";
import { createHash } from "node:crypto";
import { join } from "node:path";
import { findProofRevision } from "./catalogue-revisions.mjs";

export const NATIVE_ID = "nielstron-20261009-tightening";
export const KERNEL_DIRECTORY = "public/proofs/nielstron-20261009-kernels";
export const SOURCE_COMMIT = "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6";
export const SOURCE_MANIFEST =
  "eeef7d35e9437ad2ad5180be09bbaecf8e0403f8c16b399b868bf21818d176ed";
export const SOURCE_ARCHIVE =
  "4388d6e63f0127ce12a116ead3ffecbdc1db2a0d33b5da15993c206c69896dd4";
// Keep the receipt's original archive binding immutable. The reviewed published
// package relocates third-party notices for case-insensitive filesystems and
// updates packaging documentation; all checked source/config bytes are still
// compared individually against the original replay manifest below.
export const PUBLISHED_SOURCE_ARCHIVE =
  "bc07ecdd5994f9838accb23601604f759d6a9606db73815d66209d81ec0b6eba";
const THETA = "874957019420098946128604623/1000000000000000000000000000";
const NAMES = [
  "QRHPalomar.allDirichlet",
  "QRHPalomar.zeta",
  "QRHPalomar.allHecke",
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
const digest = (data) => createHash("sha256").update(data).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
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

export function validateNativeKernelEvidence(
  root,
  catalogue,
  evidenceDirectory,
) {
  const record = findProofRevision(catalogue, NATIVE_ID);
  if (!record) return null;
  const directory = evidenceDirectory || join(root, KERNEL_DIRECTORY);
  if (!existsSync(directory)) {
    demand(
      record.status === "verification-pending" && !record.first_verified_at,
      "Native-only result cannot claim independent kernel verification",
    );
    return null;
  }
  const bytes = (path) => {
    demand(safe(path), "Unsafe independent evidence path");
    return readFileSync(join(directory, path));
  };
  const json = (path) => JSON.parse(bytes(path));
  const collection = json("collection.json");
  demand(
    collection.schema_version === 1 &&
      collection.kind === "local-mechanical-kernel-evidence",
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
    report.status === "PASS" && report.comparator_exit_code === 0,
    "Comparator acceptance is missing",
  );
  demand(
    report.theta === THETA &&
      `${record.theta.numerator}/${record.theta.denominator}` === THETA,
    "Independent checker boundary differs from catalogue",
  );
  demand(
    report.source_commit === SOURCE_COMMIT &&
      report.source_manifest_sha256 === SOURCE_MANIFEST &&
      report.source_archive_sha256 === SOURCE_ARCHIVE,
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
      pins.driver_sha256 === collection.files[report.runner],
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
      build.modules_checked === 7232 &&
      build.qrh_modules_checked === 206 &&
      build.sources_and_oleans_rehashed === true &&
      build.challenge_imports_no_QRH === true,
    "Checker input integrity audit is incomplete",
  );
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
    Object.keys(report.export_sizes).length === 2 &&
      Object.keys(report.export_sizes).every(
        (path) => path.startsWith("exports/") && artifacts[path],
      ),
    "Both independently exported proof artifacts are required",
  );
  const canonicalChallenge = readFileSync(
    join(root, "public/proofs/palomar-20261009/qrh/src/Challenge.lean"),
    "utf8",
  ).replaceAll("874957019421 / 1000000000000", THETA.replace("/", " / "));
  demand(
    bytes(report.challenge_source).toString("utf8") === canonicalChallenge,
    "Independent Challenge differs from the inherited fixed three-target template",
  );
  const replay = JSON.parse(
    readFileSync(
      join(root, `proofs/${NATIVE_ID}/tightening/reproduction.json`),
    ),
  );
  demand(
    replay.source_manifest_sha256 === SOURCE_MANIFEST,
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
    ) === PUBLISHED_SOURCE_ARCHIVE,
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
