// Authenticate a reviewed local checking dossier; never execute submitted code.
// A website build does not replace checking, review, or a signed admission receipt.
import { readFileSync, readdirSync, lstatSync } from "node:fs";
import { createHash } from "node:crypto";
import { join } from "node:path";
import { validateMaintainerReplay } from "./maintainer-replay.mjs";

export const EXTERNAL_PINS = {
  schema_version: 1,
  entries: Object.fromEntries(
    ["argonaut-20261008", "liu-20261008"].map((id) => [
      id,
      JSON.parse(
        readFileSync(
          new URL(`./external-kernel-pins/${id}.json`, import.meta.url),
          "utf8",
        ),
      ),
    ]),
  ),
};
const AXIOMS = ["Classical.choice", "Quot.sound", "propext"];
const KERNELS = ["Lean default", "nanoda", "con-ron"];
const DECLARATIONS = [
  "QRHPalomar.allDirichlet",
  "QRHPalomar.zeta",
  "QRHPalomar.allHecke",
];
const digest = (bytes) => createHash("sha256").update(bytes).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const demand = (ok, message) => {
  if (!ok) throw Error(`External kernel evidence: ${message}`);
};
const sha = (value) =>
  typeof value === "string" && /^[a-f0-9]{64}$/.test(value);
const safe = (path) =>
  typeof path === "string" &&
  /^[A-Za-z0-9_./-]+$/.test(path) &&
  !path.startsWith("/") &&
  path.split("/").every((part) => part && part !== "." && part !== "..");
const timestamp = (value) =>
  typeof value === "string" &&
  /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$/.test(
    value,
  ) &&
  Number.isFinite(Date.parse(value));

function inventory(root, path = "") {
  demand(!lstatSync(join(root, path)).isSymbolicLink(), "symlink in dossier");
  const files = [];
  for (const name of readdirSync(join(root, path)).sort()) {
    const relative = path ? `${path}/${name}` : name;
    demand(safe(relative), "unsafe dossier filename");
    const stat = lstatSync(join(root, relative));
    demand(!stat.isSymbolicLink(), "symlink in dossier");
    if (stat.isDirectory()) files.push(...inventory(root, relative));
    else {
      demand(stat.isFile(), "non-file in dossier");
      files.push(relative);
    }
  }
  return files.sort();
}

export function validateExternalKernelEvidence(
  root,
  catalogue,
  reviewed = EXTERNAL_PINS,
) {
  demand(
    reviewed.schema_version === 1 && reviewed.entries,
    "invalid reviewed pin table",
  );
  const reports = [];
  for (const [id, pin] of Object.entries(reviewed.entries)) {
    const matches = catalogue.records.filter((record) => record.id === id);
    demand(matches.length === 1, `missing or duplicate catalogue entry ${id}`);
    const record = matches[0];
    if (id === "argonaut-20261008" && record.status === "framework-verified")
      demand(
        pin?.maintainer_replay?.replay_profile === "argonaut-v0.1.8",
        "Argonaut needs an isolated maintainer replay before verification",
      );
    if (!pin) {
      demand(
        record.status === "verification-pending" && !record.first_verified_at,
        `${id} has no reviewed independent acceptance`,
      );
      continue;
    }
    demand(
      typeof pin.repository === "string" &&
        /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(pin.repository) &&
        typeof pin.source_compiler === "string" &&
        /^\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?$/.test(pin.source_compiler) &&
        typeof pin.judge_toolchain === "string" &&
        /^\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?$/.test(pin.judge_toolchain) &&
        typeof pin.palomar_commit === "string" &&
        /^[a-f0-9]{40}$/.test(pin.palomar_commit) &&
        pin.entrypoint &&
        [
          pin.entrypoint.module,
          pin.entrypoint.declaration,
          pin.challenge_module,
          pin.solution_module,
        ].every(
          (name) =>
            typeof name === "string" &&
            /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(name),
        ),
      "incomplete reviewed checker/source pins",
    );
    demand(
      safe(pin.directory) && pin.directory.startsWith("public/proofs/"),
      "unsafe dossier directory",
    );
    // Reject symlinks at every prefix, including a symlinked proofs directory.
    let prefix = root;
    for (const part of pin.directory.split("/")) {
      prefix = join(prefix, part);
      demand(
        lstatSync(prefix).isDirectory() && !lstatSync(prefix).isSymbolicLink(),
        "unsafe dossier prefix",
      );
    }
    const directory = join(root, pin.directory);
    const bytes = (path) => {
      demand(safe(path), "unsafe artifact path");
      return readFileSync(join(directory, path));
    };
    demand(
      sha(pin.collection_sha256) &&
        digest(bytes("collection.json")) === pin.collection_sha256,
      "collection differs from reviewed pin",
    );
    const collection = JSON.parse(bytes("collection.json"));
    demand(
      collection.schema_version === 1 &&
        collection.kind === "local-mechanical-kernel-evidence" &&
        collection.files &&
        typeof collection.files === "object" &&
        !Array.isArray(collection.files),
      "invalid collection",
    );
    demand(
      !Object.hasOwn(collection.files, "collection.json"),
      "self-referential collection",
    );
    demand(
      same(
        inventory(directory),
        [...Object.keys(collection.files), "collection.json"].sort(),
      ),
      "dossier inventory differs from collection",
    );
    for (const [path, hash] of Object.entries(collection.files))
      demand(
        safe(path) && sha(hash) && digest(bytes(path)) === hash,
        `artifact checksum mismatch: ${path}`,
      );
    const json = (path) => {
      demand(
        safe(path) && sha(collection.files[path]),
        `unlisted JSON artifact: ${path}`,
      );
      return JSON.parse(bytes(path));
    };
    const report = json("result.json");
    demand(
      report.status === "PASS" &&
        report.comparator_exit_code === 0 &&
        report.judge_exit_code === 0,
      "Comparator/judge acceptance missing",
    );
    demand(
      report.palomar_preflight === "passed" &&
        report.statement_definitions_compared === true,
      "statement/definition/preflight check missing",
    );
    demand(
      same(report.kernels, KERNELS) &&
        same(report.declarations, DECLARATIONS) &&
        Array.isArray(report.allowed_axioms) &&
        same([...report.allowed_axioms].sort(), AXIOMS),
      "kernel, target or axiom scope differs",
    );
    demand(
      timestamp(report.verified_at_utc),
      "invalid actual verification time",
    );
    demand(
      report.source_commit === pin.source_commit &&
        /^[a-f0-9]{40}$/.test(pin.source_commit) &&
        record.source_commit === pin.source_commit &&
        record.repository === pin.repository,
      "source revision differs from reviewed contribution",
    );
    demand(
      same(record.entrypoint, pin.entrypoint),
      "catalogue entrypoint differs from reviewed target",
    );
    demand(
      `${record.theta.numerator}/${record.theta.denominator}` === pin.theta,
      "catalogue plotted bound differs",
    );
    if (pin.theta_exact) {
      demand(
        record.exact_bound === pin.theta_exact &&
          report.theta_exact === pin.theta_exact,
        "exact algebraic target differs",
      );
      // The plotted enclosure is not substituted for the algebraic theorem.
      demand(
        report.theta === undefined || report.theta === pin.theta,
        "report plotting endpoint differs",
      );
    } else {
      demand(
        !record.exact_bound &&
          !report.theta_exact &&
          report.theta === pin.theta,
        "rational target differs",
      );
    }
    demand(
      sha(pin.source_manifest_sha256) &&
        report.source_manifest_sha256 === pin.source_manifest_sha256,
      "checked source manifest differs",
    );
    demand(
      report.source_compiler === pin.source_compiler &&
        report.judge_toolchain === pin.judge_toolchain &&
        report.palomar_commit === pin.palomar_commit,
      "checker toolchain differs from reviewed run",
    );
    demand(
      sha(pin.challenge_sha256) &&
        collection.files[report.challenge_source] === pin.challenge_sha256,
      "canonical independent challenge differs",
    );

    const required = [
      report.challenge_source,
      report.solution_source,
      report.comparator_config,
      report.judge_log,
      report.preflight_results,
      report.tool_pins,
      report.runner,
      report.source_inputs,
      report.native_build_report,
      report.source_provenance,
      report.reproduction_script,
    ];
    demand(
      report.artifacts && typeof report.artifacts === "object",
      "missing artifact bindings",
    );
    for (const path of required)
      demand(
        safe(path) &&
          sha(collection.files[path]) &&
          report.artifacts[path] === collection.files[path],
        `required artifact is not authenticated: ${path}`,
      );
    for (const [path, hash] of Object.entries(report.artifacts)) {
      demand(safe(path) && sha(hash), "invalid artifact binding");
      if (path.startsWith("exports/"))
        demand(
          Number.isSafeInteger(report.export_sizes?.[path]) &&
            report.export_sizes[path] > 0 &&
            !collection.files[path],
          "omitted export needs its actual size/hash",
        );
      else
        demand(
          collection.files[path] === hash,
          `report artifact differs from collection: ${path}`,
        );
    }
    demand(
      Object.keys(report.export_sizes || {}).length === 2 &&
        Object.keys(report.export_sizes).every(
          (path) => path.startsWith("exports/") && sha(report.artifacts[path]),
        ),
      "both exported proof digests are required",
    );

    const config = json(report.comparator_config);
    const conron = config.external_kernels?.["con-ron"];
    const nanoda = config.external_kernels?.nanoda;
    demand(
      same(Object.keys(config).sort(), [
        "challenge_module",
        "definition_names",
        "external_kernels",
        "permitted_axioms",
        "solution_module",
        "theorem_names",
      ]) &&
        same(config.theorem_names, DECLARATIONS) &&
        same(config.definition_names, []) &&
        Array.isArray(config.permitted_axioms) &&
        same([...config.permitted_axioms].sort(), AXIOMS) &&
        same(config.external_kernels, pin.external_kernels) &&
        same(Object.keys(config.external_kernels || {}).sort(), [
          "con-ron",
          "nanoda",
        ]) &&
        Array.isArray(conron) &&
        conron.length === 2 &&
        /(?:^|\/)con-ron$/.test(conron[0]) &&
        /^--jobs=[1-9][0-9]*$/.test(conron[1]) &&
        Array.isArray(nanoda) &&
        nanoda.length === 1 &&
        /(?:^|\/)nanoda_bin$/.test(nanoda[0]) &&
        config.challenge_module === pin.challenge_module &&
        config.solution_module === pin.solution_module,
      "Comparator configuration weakens or changes the check",
    );
    const judge = bytes(report.judge_log).toString("utf8");
    demand(
      judge.includes("Your solution is okay!") &&
        KERNELS.every((name) =>
          judge.includes(`${name} kernel accepts the solution`),
        ),
      "judge log lacks all three kernel acceptances",
    );
    const controls = json(report.preflight_results).cases;
    demand(
      Array.isArray(controls) &&
        same(
          controls.map((item) => item.name),
          [
            "PalomarPreflightSolution",
            "PalomarPreflightWrong",
            "PalomarPreflightIllTyped",
          ],
        ),
      "missing positive/negative checker controls",
    );
    const [positive, mismatch, illtyped] = controls;
    for (const item of controls)
      demand(
        safe(item.log) && sha(collection.files[item.log]),
        "unlisted control log",
      );
    const positiveLog = bytes(positive.log).toString("utf8");
    demand(
      positive.exit_code === 0 &&
        positiveLog.includes("Your solution is okay!") &&
        KERNELS.every((name) =>
          positiveLog.includes(`${name} kernel accepts the solution`),
        ),
      "positive control failed",
    );
    demand(
      Number.isInteger(mismatch.exit_code) &&
        mismatch.exit_code !== 0 &&
        bytes(mismatch.log)
          .toString("utf8")
          .includes("Challenge and solution theorem statement do not match"),
      "statement mismatch was not rejected",
    );
    demand(
      Number.isInteger(illtyped.exit_code) &&
        illtyped.exit_code !== 0 &&
        bytes(illtyped.log)
          .toString("utf8")
          .includes("Lean default kernel rejected the solution"),
      "ill-typed proof was not rejected",
    );

    // The trusted collection also authenticates the detailed build inventory and
    // checker hashes; these summaries must bind that inventory to the actual run.
    const inputs = json(report.source_inputs);
    const native = json(report.native_build_report);
    const provenance = json(report.source_provenance);
    const tools = json(report.tool_pins);
    demand(
      tools.palomar_commit === pin.palomar_commit &&
        typeof tools.exporter_commit === "string" &&
        /^[a-f0-9]{40}$/.test(tools.exporter_commit) &&
        sha(tools.source_lean_sha256) &&
        sha(tools.source_exporter_sha256) &&
        [
          "lean",
          "lake",
          "leanexport",
          "leanchecker",
          "nanoda_bin",
          "con-ron",
        ].every((name) => sha(tools.judge_tools?.[name])) &&
        tools.driver_sha256 === collection.files[report.runner],
      "checker binary/exporter/runner pins incomplete",
    );
    demand(
      inputs.manifest_sha256 === report.source_manifest_sha256 &&
        inputs.files &&
        Object.keys(inputs.files).length > 0,
      "source input inventory is incomplete",
    );
    for (const [path, hash] of Object.entries(inputs.files))
      demand(safe(path) && sha(hash), "invalid source input inventory");
    demand(
      native.status === "PASS" &&
        native.sources_and_oleans_rehashed === true &&
        native.challenge_imports_no_candidate === true &&
        native.source_manifest_sha256 === report.source_manifest_sha256,
      "native source/build integrity audit incomplete",
    );
    demand(
      provenance.source_commit === pin.source_commit &&
        provenance.repository === pin.repository &&
        provenance.publication_mode === pin.publication_mode,
      "source provenance or publication mode differs",
    );
    demand(
      ["archived-source", "remote-source"].includes(pin.publication_mode),
      "unsupported source publication mode",
    );
    if (pin.publication_mode === "archived-source") {
      demand(
        safe(report.source_archive) &&
          sha(report.source_archive_sha256) &&
          collection.files[report.source_archive] ===
            report.source_archive_sha256 &&
          report.artifacts[report.source_archive] ===
            report.source_archive_sha256,
        "source archive is not authenticated",
      );
      demand(
        safe(provenance.license_file) &&
          sha(collection.files[provenance.license_file]),
        "archived source license missing",
      );
    } else {
      demand(
        !report.source_archive && !report.source_archive_sha256,
        "remote-only source must not publish a source archive",
      );
      for (const path of Object.keys(collection.files)) {
        demand(
          !/\.(?:tar(?:\.gz)?|tgz|zip|ndjson|export|olean)$/i.test(path),
          "remote-only source must not redistribute proof exports or archives",
        );
        demand(
          !path.endsWith(".lean") ||
            path === report.challenge_source ||
            path === report.solution_source,
          "remote-only source may publish only original challenge/wrapper Lean files",
        );
      }
    }
    const replay = pin.maintainer_replay
      ? validateMaintainerReplay(root, pin.maintainer_replay, pin)
      : null;
    demand(
      (record.status === "framework-verified" &&
        record.first_verified_at ===
          (replay?.first_verified_at ??
            replay?.verified_at ??
            report.verified_at_utc)) ||
        (record.status === "verification-pending" && !record.first_verified_at),
      "catalogue status/date does not match actual checker acceptance",
    );
    reports.push(report);
  }
  return reports;
}
