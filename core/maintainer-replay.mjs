// Authenticate a protected maintainer collection. This never runs proof code and
// is not a signed registry-admission protocol.
import { readFileSync, readdirSync, lstatSync } from "node:fs";
import { createHash } from "node:crypto";
import { join } from "node:path";
const digest = (bytes) => createHash("sha256").update(bytes).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const demand = (ok, message) => {
  if (!ok) throw Error(`Maintainer replay: ${message}`);
};
const sha = (value) =>
  typeof value === "string" && /^[a-f0-9]{64}$/.test(value);
const safe = (value) =>
  typeof value === "string" &&
  /^[A-Za-z0-9_./-]+$/.test(value) &&
  !value.startsWith("/") &&
  value.split("/").every((part) => part && part !== "." && part !== "..");
function filesAt(root, prefix = "") {
  const files = [];
  for (const name of readdirSync(join(root, prefix)).sort()) {
    const path = prefix ? `${prefix}/${name}` : name;
    demand(safe(path), "unsafe filename");
    const stat = lstatSync(join(root, path));
    demand(!stat.isSymbolicLink(), "symlink in evidence");
    if (stat.isDirectory()) files.push(...filesAt(root, path));
    else {
      demand(stat.isFile(), "non-file in evidence");
      files.push(path);
    }
  }
  return files.sort();
}
export function validateMaintainerReplay(root, pin, contribution) {
  const profile = pin?.replay_profile ?? "liu-algebraic-v1";
  demand(
    ["liu-algebraic-v1", "argonaut-v0.1.8"].includes(profile),
    "unknown replay profile",
  );
  const argonaut = profile === "argonaut-v0.1.8";
  const driverDirectory = `verifier/${argonaut ? "argonaut" : "liu"}`;
  const targetNamespace = argonaut ? "QRHBoundsPR4" : "QRHBoundsPR3";
  demand(
    pin && safe(pin.directory) && pin.directory.startsWith("public/proofs/"),
    "missing reviewed replay pin",
  );
  let directory = root;
  for (const part of pin.directory.split("/")) {
    directory = join(directory, part);
    const stat = lstatSync(directory);
    demand(
      stat.isDirectory() && !stat.isSymbolicLink(),
      "unsafe evidence prefix",
    );
  }
  const read = (name) => {
    demand(safe(name), "unsafe artifact path");
    const stat = lstatSync(join(directory, name));
    demand(stat.isFile() && !stat.isSymbolicLink(), "unsafe artifact file");
    return readFileSync(join(directory, name));
  };
  demand(
    sha(pin.collection_sha256) &&
      digest(read("collection.json")) === pin.collection_sha256,
    "collection differs from reviewed pin",
  );
  const collection = JSON.parse(read("collection.json"));
  demand(
    collection.schema_version === 1 &&
      collection.kind === "independent-maintainer-replay",
    "wrong collection kind",
  );
  demand(
    collection.files &&
      typeof collection.files === "object" &&
      !Array.isArray(collection.files) &&
      !Object.hasOwn(collection.files, "collection.json"),
    "invalid inventory",
  );
  demand(
    same(
      filesAt(directory),
      [...Object.keys(collection.files), "collection.json"].sort(),
    ),
    "unlisted or missing evidence",
  );
  for (const [name, hash] of Object.entries(collection.files)) {
    demand(
      safe(name) && sha(hash) && digest(read(name)) === hash,
      "artifact checksum mismatch",
    );
    demand(
      !/\.(?:export|olean|ndjson|tar|tgz|zip)(?:\.gz)?$/i.test(name),
      "unlicensed source/export archive",
    );
    demand(
      !name.endsWith(".lean") ||
        ["challenge-src/Challenge.lean", "solution-src/Solution.lean"].includes(
          name,
        ),
      "unlicensed candidate source",
    );
  }
  const report = JSON.parse(read("result.json"));
  demand(
    sha(pin.receipt_sha256) &&
      collection.files["result.json"] === pin.receipt_sha256,
    "receipt differs from reviewed run",
  );
  demand(
    report.status === "PASS" && report.judge_exit_code === 0,
    "no checker acceptance",
  );
  demand(
    report.source_commit === contribution.source_commit &&
      report.source_repository ===
        `https://github.com/${contribution.repository}`,
    "source revision differs",
  );
  demand(
    report.theta_exact === pin.theta_exact &&
      report.source_content_sha256 === pin.source_content_sha256,
    "source content or exact bound differs",
  );
  demand(
    report.driver_sha256 === pin.driver_sha256 &&
      report.pins_sha256 === pin.pins_sha256,
    "driver or dependency pins differ",
  );
  demand(
    digest(readFileSync(join(root, driverDirectory, "replay.py"))) ===
      pin.driver_sha256 &&
      digest(readFileSync(join(root, driverDirectory, "pins.json"))) ===
        pin.pins_sha256,
    "current replay differs from tested driver",
  );
  demand(
    report.source_compiler === contribution.source_compiler &&
      report.judge_toolchain === contribution.judge_toolchain &&
      report.verifier_commit === contribution.palomar_commit,
    "toolchain differs",
  );
  demand(
    same(report.kernels, ["Lean default", "nanoda", "con-ron"]) &&
      same(report.allowed_axioms, [
        "Classical.choice",
        "Quot.sound",
        "propext",
      ]),
    "kernel or axiom scope differs",
  );
  demand(
    same(report.targets, [
      `${targetNamespace}.allDirichlet`,
      `${targetNamespace}.zeta`,
      `${targetNamespace}.allHecke`,
    ]),
    "target scope differs",
  );
  demand(
    report.sandbox_preflight === "PASS" &&
      report.candidate_mount_preflight === "PASS" &&
      report.receipt_outside_candidate === true &&
      report.challenge_exported_before_candidate_execution === true,
    "isolation or challenge ordering missing",
  );
  demand(
    report.candidate_modules_rebuilt === (argonaut ? 152 : 238) &&
      report.approved_dependency_modules === 7026 &&
      report.extra_official_cache_modules === 4807,
    "dependency/build scope differs",
  );
  if (argonaut) {
    const inputs = JSON.parse(
      readFileSync(join(root, driverDirectory, "pins.json")),
    );
    demand(
      contribution.repository ===
        "Argonaut-Math/argonaut-math-quasi-riemann-boundary" &&
        report.theta_exact === contribution.theta &&
        report.theta_exact === inputs.theta_exact &&
        report.reviewed_pr_head === inputs.pr_head_commit &&
        report.trusted_base_commit === inputs.trusted_base_commit &&
        same(report.release, inputs.release) &&
        report.release?.sha256 === report.source_content_sha256,
      "Argonaut source release, revision or exact bound differs",
    );
  }
  demand(
    typeof report.verified_at === "string" &&
      /^\d{4}-\d{2}-\d{2}T.*(?:Z|[+-]\d{2}:\d{2})$/.test(report.verified_at) &&
      Number.isFinite(Date.parse(report.verified_at)),
    "invalid verification time",
  );
  demand(
    report.artifacts &&
      collection.artifact_publication &&
      same(
        Object.keys(report.artifacts).sort(),
        Object.keys(collection.artifact_publication).sort(),
      ),
    "receipt artifact inventory differs",
  );
  const transformations = collection.files["publication-transformations.json"]
    ? JSON.parse(read("publication-transformations.json")).changes
    : [];
  demand(Array.isArray(transformations), "invalid publication transformations");
  for (const [name, hash] of Object.entries(report.artifacts)) {
    demand(safe(name) && sha(hash), "invalid original artifact");
    const publication = collection.artifact_publication[name];
    demand(
      publication.original_sha256 === hash,
      "original receipt binding differs",
    );
    if (name.startsWith("exports/"))
      demand(
        publication.path === null &&
          ["exports/Challenge.export", "exports/Solution.export"].includes(
            name,
          ),
        "proof export must remain private",
      );
    else {
      demand(
        safe(publication.path) && sha(collection.files[publication.path]),
        "bound artifact is unavailable",
      );
      if (collection.files[publication.path] !== hash) {
        const changes = transformations.filter(
          (item) => item.path === publication.path,
        );
        demand(
          changes.length === 1 &&
            changes[0].original_sha256 === hash &&
            changes[0].published_sha256 === collection.files[publication.path],
          "path neutralization lost its original receipt binding",
        );
      }
    }
  }
  for (const name of [
    "exports/Challenge.export",
    "exports/Solution.export",
    "logs/judge.log",
    "challenge-frozen.json",
    "preflight-result.json",
    "source-manifest.json",
    "tool-pins.json",
    "dependency-pins.json",
    "trusted-library-manifest.json",
    "comparator.json",
  ])
    demand(
      sha(report.artifacts[name]),
      `required receipt binding missing: ${name}`,
    );
  const published = (name) => read(collection.artifact_publication[name].path);
  demand(
    digest(published("challenge-src/Challenge.lean")) === pin.challenge_sha256,
    "trusted challenge differs",
  );
  const frozen = JSON.parse(published("challenge-frozen.json"));
  demand(
    frozen.source_sha256 === pin.challenge_sha256 &&
      frozen.export_sha256 === report.artifacts["exports/Challenge.export"] &&
      frozen.exported_before_candidate_execution,
    "frozen challenge binding differs",
  );
  const config = JSON.parse(published("comparator.json"));
  demand(
    same(Object.keys(config).sort(), [
      "challenge_module",
      "definition_names",
      "external_kernels",
      "permitted_axioms",
      "solution_module",
      "theorem_names",
    ]) &&
      same(config.theorem_names, report.targets) &&
      same(config.definition_names, []) &&
      same(config.permitted_axioms, report.allowed_axioms) &&
      config.challenge_module === "Challenge" &&
      config.solution_module === "Solution" &&
      same(Object.keys(config.external_kernels).sort(), ["con-ron", "nanoda"]),
    "Comparator configuration differs",
  );
  const log = published("logs/judge.log").toString("utf8");
  demand(
    log.includes("Your solution is okay!") &&
      report.kernels.every((name) =>
        log.includes(`${name} kernel accepts the solution`),
      ),
    "kernel acceptance logs missing",
  );
  const controls = JSON.parse(read("controls/control-results.json"));
  demand(
    controls.status === "PASS" &&
      controls.main_receipt_sha256 === pin.receipt_sha256 &&
      Array.isArray(controls.cases) &&
      same(
        controls.cases.map((item) => item.name),
        [
          "PalomarPreflightSolution",
          "PalomarPreflightWrong",
          "PalomarPreflightIllTyped",
        ],
      ),
    "fresh checker controls missing or unbound",
  );
  const controlLog = (item) => {
    demand(
      safe(item.log) && sha(collection.files[`controls/${item.log}`]),
      "unlisted checker control log",
    );
    return read(`controls/${item.log}`).toString("utf8");
  };
  const [positive, mismatch, illtyped] = controls.cases;
  const accepted = controlLog(positive);
  demand(
    positive.exit_code === 0 &&
      accepted.includes("Your solution is okay!") &&
      report.kernels.every((name) =>
        accepted.includes(`${name} kernel accepts the solution`),
      ),
    "fresh positive control failed",
  );
  demand(
    mismatch.exit_code === 1 &&
      controlLog(mismatch).includes(
        "Challenge and solution theorem statement do not match",
      ),
    "fresh statement mismatch control failed",
  );
  demand(
    illtyped.exit_code === 1 &&
      controlLog(illtyped).includes(
        "Lean default kernel rejected the solution",
      ),
    "fresh ill-typed control failed",
  );
  let firstVerifiedAt = report.verified_at;
  if (pin.first_acceptance) {
    const firstPin = pin.first_acceptance;
    for (const name of [firstPin.receipt, firstPin.driver, firstPin.log])
      demand(
        safe(name) && sha(collection.files[name]),
        "unlisted first acceptance evidence",
      );
    demand(
      collection.files[firstPin.receipt] === firstPin.receipt_sha256,
      "first acceptance receipt differs",
    );
    const first = JSON.parse(read(firstPin.receipt));
    demand(
      first.status === "PASS" &&
        first.judge_exit_code === 0 &&
        first.driver_sha256 === collection.files[firstPin.driver] &&
        first.artifacts?.["logs/judge.log"] === collection.files[firstPin.log],
      "first acceptance driver or log differs",
    );
    for (const key of [
      "source_commit",
      "source_repository",
      "source_content_sha256",
      "reviewed_pr_head",
      "trusted_base_commit",
      "pins_sha256",
      "theta_exact",
      "targets",
      "kernels",
      "allowed_axioms",
      "source_compiler",
      "judge_toolchain",
      "verifier_commit",
      "sandbox_preflight",
      "candidate_mount_preflight",
      "receipt_outside_candidate",
      "challenge_exported_before_candidate_execution",
      "candidate_modules_rebuilt",
      "approved_dependency_modules",
      "extra_official_cache_modules",
    ])
      demand(
        same(first[key], report[key]),
        "first acceptance proves a different source or scope",
      );
    const firstLog = read(firstPin.log).toString("utf8");
    for (const name of [
      "challenge-src/Challenge.lean",
      "solution-src/Solution.lean",
      "dependency-pins.json",
      "trusted-library-manifest.json",
    ])
      demand(
        sha(first.artifacts?.[name]) &&
          first.artifacts[name] === report.artifacts[name],
        "first acceptance challenge or dependencies differ",
      );
    demand(
      firstLog.includes("Your solution is okay!") &&
        report.kernels.every((name) =>
          firstLog.includes(`${name} kernel accepts the solution`),
        ),
      "first kernel acceptance missing",
    );
    demand(
      typeof first.verified_at === "string" &&
        /^\d{4}-\d{2}-\d{2}T.*(?:Z|[+-]\d{2}:\d{2})$/.test(first.verified_at) &&
        first.verified_at === firstPin.verified_at &&
        Number.isFinite(Date.parse(first.verified_at)) &&
        Date.parse(first.verified_at) <= Date.parse(report.verified_at),
      "invalid first acceptance time",
    );
    firstVerifiedAt = first.verified_at;
  }
  return { ...report, first_verified_at: firstVerifiedAt };
}
