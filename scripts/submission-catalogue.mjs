// Build from the checked-out submissions. Admission checks decide what may be
// merged; rendering a checkout never contacts GitHub or walks commit history.
import { execFileSync } from "node:child_process";
import {
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  writeFileSync,
} from "node:fs";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import {
  boundLabel,
  validateCatalogue,
  withSubmissionTimeline,
} from "../core/catalogue.mjs";
import { proofRevision } from "../core/catalogue-revisions.mjs";
import { algebraicProfiles, exactBound } from "../core/exact-bound.mjs";
import { reduced } from "../core/rational.mjs";
import { historicalCertificate } from "../verifier/certificate.mjs";
import { submissionFiles } from "../verifier/manifest.mjs";
import {
  parseSubmissionMetadataJSON,
  validateSubmissionMetadata,
} from "../verifier/submission-metadata.mjs";
import { submissionDirectories } from "../verifier/submission-paths.mjs";
import { readLocalPublications } from "./local-publications.mjs";

const json = (value) => JSON.stringify(value, null, 2) + "\n";
const isSha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");
const isRepository = (value) => /^[\w.-]+\/[\w.-]+$/.test(value ?? "");

// Lean comments nest. Removing comments and strings before reading a theorem
// signature prevents examples or commented-out declarations becoming bounds.
function leanCode(source) {
  let result = "",
    index = 0,
    depth = 0,
    quoted = false;
  while (index < source.length) {
    const pair = source.slice(index, index + 2);
    if (depth) {
      if (pair === "/-") {
        depth++;
        index += 2;
      } else if (pair === "-/") {
        depth--;
        index += 2;
      } else {
        result += source[index] === "\n" ? "\n" : " ";
        index++;
      }
    } else if (quoted) {
      if (source[index] === "\\") index += 2;
      else if (source[index++] === '"') quoted = false;
      result += " ";
    } else if (pair === "/-") {
      depth = 1;
      result += " ";
      index += 2;
    } else if (pair === "--") {
      const end = source.indexOf("\n", index + 2);
      index = end === -1 ? source.length : end;
      result += " ";
    } else if (source[index] === '"') {
      quoted = true;
      result += " ";
      index++;
    } else result += source[index++];
  }
  if (depth || quoted) throw Error("Unterminated Lean comment or string");
  return result;
}

// This reads the standard public entrypoint as data; it is not a proof checker.
// The six older wrappers explicitly export their bound from a local module.
export function submissionBound(sourceRoot) {
  const seen = new Set();
  const readModule = (module) => {
    if (
      !/^(Candidate|Submissions)(?:\.[A-Za-z_][A-Za-z0-9_]*)+$/.test(module) ||
      seen.has(module) ||
      seen.size >= 16
    )
      throw Error("Invalid or cyclic bound export");
    seen.add(module);
    const components = module.split(".");
    for (let count = 1; count <= components.length; count++) {
      const path = join(
        sourceRoot,
        ...components.slice(0, count - 1),
        components[count - 1] + (count === components.length ? ".lean" : ""),
      );
      const stat = lstatSync(path);
      if (
        stat.isSymbolicLink() ||
        !(count === components.length ? stat.isFile() : stat.isDirectory())
      )
        throw Error("Bound modules must be regular local source files");
    }
    const source = leanCode(
      readFileSync(join(sourceRoot, ...components) + ".lean", "utf8"),
    );
    const declarations = [...source.matchAll(/\btheorem\s+bound\b/g)];
    if (declarations.length > 1) throw Error("Ambiguous bound declaration");
    if (declarations.length) {
      const signature = source
        .slice(declarations[0].index + declarations[0][0].length)
        .split(":=", 1)[0];
      const matches = [
        ...signature.matchAll(
          /\(\s*(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»)\s*:\s*\(\s*(?:(\d+)\s*\/\s*(\d+)|([^:]+?))\s*:\s*ℝ\s*\)\s*<\s*(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»)\.re\s*\)/gu,
        ),
      ];
      if (matches.length !== 1)
        throw Error(`Cannot read the canonical exact bound in ${module}`);
      const profile = [...algebraicProfiles.values()].find(
        (p) => p.lean === matches[0][3],
      );
      if (profile) return exactBound(profile.label);
      if (matches[0][3])
        throw Error(`Cannot read the canonical exact bound in ${module}`);
      if (matches[0][1].length > 200 || matches[0][2].length > 200)
        throw Error("Exact bound integers exceed the catalogue limit");
      const theta = reduced(BigInt(matches[0][1]), BigInt(matches[0][2]));
      return exactBound(`${theta.numerator}/${theta.denominator}`);
    }
    const exports = [
      ...source.matchAll(
        /\bexport\s+((?:Candidate|Submissions)(?:\.[A-Za-z_][A-Za-z0-9_]*)+)\s*\(\s*bound\s*\)/g,
      ),
    ];
    if (exports.length !== 1)
      throw Error(`Missing canonical bound declaration or export in ${module}`);
    const target = exports[0][1];
    const imports = [...source.matchAll(/^\s*import\s+([^\n]+)/gm)].flatMap(
      (match) => match[1].trim().split(/\s+/),
    );
    const imported = imports.find(
      (module) => module === target || module === `${target}.Main`,
    );
    if (!imported)
      throw Error("Bound export must name an explicitly imported local module");
    return readModule(imported);
  };
  return readModule("Candidate.Main");
}

function git(root, args) {
  try {
    return execFileSync("git", ["--no-replace-objects", ...args], {
      cwd: root,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  } catch (error) {
    if (error.code === "ENOENT" || error.status === 1 || error.status === 128)
      return "";
    throw error;
  }
}

function checkoutRepository(root, repository) {
  if (repository === undefined) {
    const configPath = join(root, "site.config.json");
    repository = existsSync(configPath)
      ? JSON.parse(readFileSync(configPath, "utf8")).repository
      : process.env.GITHUB_REPOSITORY;
  }
  if (
    repository !== undefined &&
    repository !== null &&
    !isRepository(repository)
  )
    throw Error("Invalid repository");
  return repository || "";
}

function submissionEntries(root) {
  const directory = join(root, "submissions");
  const entries = readdirSync(directory, { withFileTypes: true });
  if (entries.some((entry) => !entry.isDirectory()))
    throw Error("Submissions must contain regular directories");
  const submissions = new Map();
  for (const [id, name] of submissionDirectories(
    entries.map((entry) => entry.name),
  )) {
    const base = join(directory, name);
    submissionFiles(base);
    const metadata = parseSubmissionMetadataJSON(
      readFileSync(join(base, "metadata.json")),
    );
    if (metadata.id !== undefined) {
      if (proofRevision(metadata) !== id)
        throw Error(`Submission metadata path differs from revision: ${name}`);
    } else validateSubmissionMetadata(metadata);
    submissions.set(id, { name, metadata });
  }
  return submissions;
}

export function readSubmissions(root = process.cwd()) {
  return new Map(
    [...submissionEntries(root)].map(([id, { metadata }]) => [id, metadata]),
  );
}

export function buildSubmissionCatalogue({
  root = process.cwd(),
  repository,
} = {}) {
  root = resolve(root);
  repository = checkoutRepository(root, repository);
  const publications = readLocalPublications(root);
  const sourceCommit = git(root, ["rev-parse", "HEAD"]);
  const directory = join(root, "submissions");
  const records = [],
    historical = [],
    certificates = new Map();
  for (const [id, { name, metadata }] of submissionEntries(root)) {
    const base = join(directory, name);
    if (metadata.id !== undefined) {
      const {
        historical: archived,
        dependencies,
        verification,
        agent_traces,
        ...original
      } = structuredClone(metadata);
      const record = withSubmissionTimeline(original);
      if (proofRevision(record) !== id)
        throw Error(`Submission metadata path differs from revision: ${name}`);
      (archived === true ? historical : records).push(record);
      if (record.status === "framework-verified")
        certificates.set(id, historicalCertificate(metadata));
      continue;
    }
    const date = /^(\d{4}-\d{2}-\d{2})-/.exec(name)?.[1];
    if (!date)
      throw Error(`Modern submission requires a dated directory: ${name}`);
    const { lean: _, ...bound } = submissionBound(join(base, "src"));
    const facts = Object.hasOwn(publications, id)
      ? publications[id].find(
          (publication) =>
            publication.certificate.theta_exact === boundLabel(bound),
        )
      : undefined;
    const evidence = facts?.certificate;
    const sourceRepository = evidence?.source_repository || repository;
    const sourcePath = evidence ? facts.source_path : `submissions/${name}/src`;
    // A local preview can contain source that HEAD does not contain. Link a
    // commit only when the entire local source tree is tracked and unchanged.
    const sourceTracked =
      evidence ||
      (isSha(sourceCommit) &&
        /^040000 tree /.test(
          git(root, ["ls-tree", sourceCommit, "--", sourcePath]),
        ));
    const dirtySource =
      !evidence &&
      git(root, [
        "status",
        "--porcelain=v1",
        "--untracked-files=normal",
        "--",
        sourcePath,
      ]);
    const pinnedCommit =
      evidence?.source_commit ||
      (sourceTracked && !dirtySource ? sourceCommit : "");
    const pr = evidence ? facts.pr : null;
    const solution =
      sourceRepository && isSha(pinnedCommit)
        ? `https://github.com/${sourceRepository}/blob/${pinnedCommit}/${sourcePath}/Candidate/Main.lean`
        : undefined;
    const certificateUrl = evidence ? `certificates/${id}.json` : undefined;
    const references = [
      ...new Map(
        [
          ...(certificateUrl
            ? [{ label: "Verification record", url: certificateUrl }]
            : []),
          ...(solution ? [{ label: "Lean source", url: solution }] : []),
          ...(repository && pr
            ? [
                {
                  label: "Submission PR",
                  url: `https://github.com/${repository}/pull/${pr}`,
                },
              ]
            : []),
          ...(metadata.references || []),
        ].map((reference) => [reference.url, reference]),
      ).values(),
    ];
    if (!references.length && sourceRepository)
      references.push({
        label: "Repository",
        url: `https://github.com/${sourceRepository}`,
      });
    if (!references.length)
      throw Error(`Submission needs a repository or source reference: ${id}`);
    records.push(
      withSubmissionTimeline({
        id,
        title: metadata.title,
        ...bound,
        authors: metadata.authors,
        method: metadata.description,
        license: metadata.license || "See submitted source notices",
        builds_on: metadata.builds_on || [],
        status: evidence ? "framework-verified" : "accepted",
        submitted_at: evidence ? facts.submitted_at : "",
        published_at: metadata.published_at || "",
        merged_at: "",
        pr: pr || null,
        repository: sourceRepository,
        source_commit: isSha(pinnedCommit) ? pinnedCommit : "",
        first_verified_at: evidence?.verified_at || "",
        timeline_at: `${date}T00:00:00Z`,
        date_label: "Public announcement",
        ...(!metadata.published_at && !evidence
          ? { date_precision: "day" }
          : {}),
        entrypoint: {
          module: "Candidate.Main",
          declaration: "Candidate.bound",
        },
        verification_note: evidence
          ? `Comparator checked the canonical all-Dirichlet statement at ${evidence.theta_exact} for the submitted commit. Lean, NanoDa and con-ron accepted the proof in the standard sandbox.`
          : "Proof verification is required before merge. A verification timestamp is not recorded for this entry.",
        ...(certificateUrl ? { certificate_url: certificateUrl } : {}),
        ...(solution ? { solution_url: solution } : {}),
        references,
      }),
    );
    if (evidence) certificates.set(id, evidence);
  }
  const byDate = (a, b) =>
    Date.parse(a.timeline_at) - Date.parse(b.timeline_at) ||
    a.id.localeCompare(b.id);
  records.sort(byDate);
  historical.sort(byDate);
  const dates = [...records, ...historical].flatMap((record) =>
    [record.timeline_at, record.first_verified_at].filter((date) =>
      Number.isFinite(Date.parse(date)),
    ),
  );
  const catalogue = validateCatalogue({
    schema_version: 1,
    ...(dates.length
      ? {
          as_of: new Date(Math.max(...dates.map(Date.parse)))
            .toISOString()
            .slice(0, 10),
        }
      : {}),
    records,
    ...(historical.length ? { historical_records: historical } : {}),
  });
  // Validate all source metadata before updating any generated output.
  for (const [id, evidence] of certificates) {
    mkdirSync(join(root, "public/certificates"), { recursive: true });
    writeFileSync(join(root, `public/certificates/${id}.json`), json(evidence));
  }
  mkdirSync(join(root, "catalogue"), { recursive: true });
  writeFileSync(join(root, "catalogue/results.json"), json(catalogue));
  return catalogue;
}

if (
  process.argv[1] &&
  import.meta.url === pathToFileURL(resolve(process.argv[1])).href
) {
  const catalogue = buildSubmissionCatalogue();
  console.log(
    `Catalogue: ${catalogue.records.length} results from local submissions.`,
  );
}
