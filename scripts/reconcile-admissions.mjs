// Generate the public catalogue from per-proof metadata and durable admissions.
// The archive is read as data; no submitted project or archived code is executed.
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  lstatSync,
  readFileSync,
  readdirSync,
  writeFileSync,
} from "node:fs";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { isDeepStrictEqual } from "node:util";
import {
  boundLabel,
  validateCatalogue,
  withSubmissionTimeline,
} from "../core/catalogue.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import {
  ADMISSION_BRANCH,
  admissionPath,
  validateAdmissionRecord,
} from "../verifier/admission-archive.mjs";
import {
  certificate,
  historicalCertificate,
} from "../verifier/certificate.mjs";
import { validateSubmissionMetadata } from "../verifier/submission-metadata.mjs";
import { submissionFiles } from "../verifier/manifest.mjs";
import { publicationRecord } from "../verifier/publication-record.mjs";

const isSha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");
const isRepository = (value) => /^[\w.-]+\/[\w.-]+$/.test(value ?? "");
const maxRecordBytes = 8 * 1024 * 1024;
const cachePath = ".work/admission-records.json";
const json = (value) => JSON.stringify(value, null, 2) + "\n";

function eligibleAdmissions(admissions) {
  const unique = new Map();
  for (const admission of admissions) {
    validateAdmissionRecord(admission);
    if (!Number.isFinite(Date.parse(admission.merged_at)))
      throw Error(`Missing admission merge date: ${admission.result_id}`);
    if (!isSha(admission.merge_commit_sha))
      throw Error(`Missing admission merge commit: ${admission.result_id}`);
    // GitHub's merge timestamp has second precision; archive times include ms.
    if (
      Math.floor(Date.parse(admission.admission.archived_at) / 1000) >
      Math.floor(Date.parse(admission.merged_at) / 1000)
    )
      continue;
    const key = admissionPath(admission);
    const previous = unique.get(key);
    if (previous && !isDeepStrictEqual(previous, admission))
      throw Error(`Conflicting immutable admission: ${admission.result_id}`);
    unique.set(key, admission);
  }
  return [...unique.values()];
}

function archiveOrder(a, b) {
  return (
    Date.parse(a.admission.archived_at) - Date.parse(b.admission.archived_at) ||
    (BigInt(a.admission.run_id) > BigInt(b.admission.run_id)
      ? 1
      : BigInt(a.admission.run_id) < BigInt(b.admission.run_id)
        ? -1
        : Number(
            BigInt(a.admission.run_attempt) - BigInt(b.admission.run_attempt),
          ))
  );
}

function selectedAdmissions(admissions) {
  const selected = new Map();
  for (const admission of eligibleAdmissions(admissions)) {
    const key = `${admission.number}/${admission.head_sha}/${admission.result_id}`;
    const pair = selected.get(key);
    if (!pair) {
      selected.set(key, { admission, verification: admission });
      continue;
    }
    // A timestamp from a different statement/source is never reusable evidence.
    const old = pair.admission;
    if (
      admission.repository !== old.repository ||
      admission.theta_exact !== old.theta_exact ||
      admission.source_tree !== old.source_tree ||
      admission.pr.created_at !== old.pr.created_at
    )
      throw Error(
        `Conflicting admitted proof identity: ${admission.result_id}`,
      );
    if (archiveOrder(admission, old) > 0) pair.admission = admission;
    if (
      (Date.parse(admission.certificate.verified_at) -
        Date.parse(pair.verification.certificate.verified_at) ||
        archiveOrder(admission, pair.verification)) < 0
    )
      pair.verification = admission;
  }
  return [...selected.values()];
}

// admissions contains only envelopes whose merge and source were authenticated
// by the online reconciler, with merged_at added to its local cache.
export function generateCatalogue({
  legacy,
  admissions,
  metadataById = new Map(),
}) {
  if (!Array.isArray(legacy) || !Array.isArray(admissions))
    throw Error("Invalid catalogue inputs");
  const records = [],
    historical = [],
    revisions = new Map();
  for (const input of legacy) {
    const {
      historical: isHistorical,
      dependencies,
      verification,
      ...original
    } = structuredClone(input);
    const record = withSubmissionTimeline(original);
    const revision = proofRevision(record);
    if (revisions.has(revision))
      throw Error(`Duplicate proof metadata: ${revision}`);
    revisions.set(revision, record);
    (isHistorical === true ? historical : records).push(record);
  }
  const generated = new Map();
  const sorted = selectedAdmissions(admissions).sort(
    (a, b) =>
      Date.parse(a.verification.certificate.verified_at) -
        Date.parse(b.verification.certificate.verified_at) ||
      String(a.admission.result_id).localeCompare(
        String(b.admission.result_id),
      ) ||
      String(a.admission.head_sha).localeCompare(
        String(b.admission.head_sha),
      ) ||
      a.admission.number - b.admission.number,
  );
  for (const { admission: input, verification } of sorted) {
    const admission = validateAdmissionRecord(input);
    const old = revisions.get(admission.result_id);
    if (old) {
      if (boundLabel(old) !== admission.theta_exact)
        throw Error(`Conflicting exact bound for ${admission.result_id}`);
      const previous = generated.get(admission.result_id);
      if (previous && previous.source_tree !== admission.source_tree)
        throw Error(`Conflicting admitted source for ${admission.result_id}`);
      // Reviewed legacy metadata and its original evidence remain authoritative.
      continue;
    }
    if (records.some((record) => record.id === admission.result_id))
      throw Error(
        `Admission conflicts with a proof revision: ${admission.result_id}`,
      );
    const record = publicationRecord(
      {
        ...admission,
        metadata: metadataById.get(admission.result_id) ?? admission.metadata,
      },
      verification,
    );
    records.push(record);
    revisions.set(admission.result_id, record);
    generated.set(admission.result_id, admission);
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
  const asOf = dates.length
    ? new Date(Math.max(...dates.map(Date.parse))).toISOString().slice(0, 10)
    : null;
  return validateCatalogue({
    schema_version: 1,
    ...(asOf ? { as_of: asOf } : {}),
    records,
    ...(historical.length ? { historical_records: historical } : {}),
  });
}

function github({ repository, token, fetcher }) {
  return async (route, allowMissing = false) => {
    const response = await fetcher(
      `https://api.github.com/repos/${repository}/${route}`,
      {
        headers: {
          Accept: "application/vnd.github+json",
          "X-GitHub-Api-Version": "2022-11-28",
          Authorization: `Bearer ${token}`,
        },
      },
    );
    if (allowMissing && response.status === 404) return null;
    if (!response.ok)
      throw Error(
        `Admission reconciliation API failed: HTTP ${response.status}`,
      );
    return response.json();
  };
}

async function archiveRecords(request) {
  const ref = await request(`git/ref/heads/${ADMISSION_BRANCH}`, true);
  if (!ref) return [];
  if (!isSha(ref.object?.sha)) throw Error("Invalid admission archive ref");
  const commit = await request(`git/commits/${ref.object.sha}`);
  if (!isSha(commit.tree?.sha)) throw Error("Invalid admission archive commit");
  const tree = await request(`git/trees/${commit.tree.sha}?recursive=1`);
  if (tree.truncated || !Array.isArray(tree.tree))
    throw Error("Incomplete admission archive tree");
  const entries = tree.tree.filter(
    (entry) => entry.path?.startsWith("records/") && entry.type !== "tree",
  );
  if (new Set(entries.map((entry) => entry.path)).size !== entries.length)
    throw Error("Duplicate admission archive path");
  const records = [];
  for (const entry of entries) {
    if (
      entry.type !== "blob" ||
      entry.mode !== "100644" ||
      !isSha(entry.sha) ||
      !/^records\/[1-9][0-9]*\/[a-f0-9]{40}\/[a-z][a-z0-9-]{2,63}\/[1-9][0-9]*-[1-9][0-9]*\.json$/.test(
        entry.path,
      ) ||
      entry.size > maxRecordBytes
    )
      throw Error("Invalid admission archive file");
    const blob = await request(`git/blobs/${entry.sha}`);
    if (
      blob.encoding !== "base64" ||
      typeof blob.content !== "string" ||
      blob.size > maxRecordBytes
    )
      throw Error("Invalid admission archive blob");
    const bytes = Buffer.from(blob.content, "base64");
    if (bytes.length > maxRecordBytes)
      throw Error("Admission archive record is too large");
    const record = validateAdmissionRecord(JSON.parse(bytes.toString("utf8")));
    if (admissionPath(record) !== entry.path)
      throw Error("Admission archive path differs from record");
    records.push(record);
  }
  return records;
}

function gitRead(root, args) {
  return execFileSync("git", args, {
    cwd: root,
    encoding: "utf8",
    env: { ...process.env, GIT_NO_REPLACE_OBJECTS: "1" },
    stdio: ["ignore", "pipe", "pipe"],
    maxBuffer: 32 * 1024 * 1024,
  });
}

function sourceTree(root, admission) {
  try {
    gitRead(root, [
      "merge-base",
      "--is-ancestor",
      admission.merge_commit_sha,
      "HEAD",
    ]);
  } catch (error) {
    // A concurrent merge may be newer than this checkout (and its fetched
    // objects). Publish it only once the build includes the actual merge.
    if (error.status === 1 || error.status === 128) return false;
    throw error;
  }
  const entry = gitRead(root, [
    "ls-tree",
    admission.merge_commit_sha,
    "--",
    admission.source_path,
  ]).trimEnd();
  const expected = `040000 tree ${admission.source_tree}\t${admission.source_path}`;
  if (entry !== expected)
    throw Error(
      `Merged source differs from verified admission: ${admission.result_id}`,
    );
  for (const [id, tree] of Object.entries(admission.dependency_trees ?? {})) {
    const path = `submissions/${id}`;
    const entry = gitRead(root, [
      "ls-tree",
      admission.merge_commit_sha,
      "--",
      path,
    ]).trimEnd();
    if (entry !== `040000 tree ${tree}\t${path}`)
      throw Error(`Merged dependency differs from verified admission: ${id}`);
  }
  return true;
}

export function readSubmissions(root) {
  const directory = join(root, "submissions");
  if (!existsSync(directory)) return new Map();
  if (!lstatSync(directory).isDirectory())
    throw Error("Expected a regular submissions directory");
  const submissions = new Map();
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    if (!entry.isDirectory() || !/^[a-z][a-z0-9-]{2,63}$/.test(entry.name))
      throw Error(`Invalid submission directory: ${entry.name}`);
    const base = join(directory, entry.name);
    submissionFiles(base);
    const metadata = JSON.parse(
      readFileSync(join(base, "metadata.json"), "utf8"),
    );
    if (metadata.id !== undefined) {
      if (proofRevision(metadata) !== entry.name)
        throw Error(
          `Submission metadata path differs from revision: ${entry.name}`,
        );
    } else validateSubmissionMetadata(metadata);
    submissions.set(entry.name, metadata);
  }
  return submissions;
}

export async function reconcileAdmissions({
  root = process.cwd(),
  repository = process.env.GITHUB_REPOSITORY,
  defaultBranch = process.env.QRH_DEFAULT_BRANCH,
  online = false,
  fetcher = fetch,
  token = process.env.GITHUB_TOKEN,
} = {}) {
  const submissions = readSubmissions(root);
  const legacy = [...submissions.values()].filter(
    (metadata) => metadata.id !== undefined,
  );
  const legacyIds = new Set(legacy.map(proofRevision));
  let admissions;
  if (online) {
    if (!isRepository(repository) || !defaultBranch || !token)
      throw Error(
        "Online admission reconciliation requires repository credentials and default branch",
      );
    const request = github({ repository, token, fetcher });
    const archived = await archiveRecords(request);
    const pulls = new Map();
    admissions = [];
    for (const record of archived) {
      if (record.repository !== repository)
        throw Error("Admission archive belongs to a different repository");
      if (!pulls.has(record.number))
        pulls.set(record.number, await request(`pulls/${record.number}`));
      const pr = pulls.get(record.number);
      // Old heads and unmerged submissions are routinely present in the archive.
      if (
        !pr.merged ||
        pr.head?.sha !== record.head_sha ||
        pr.base?.ref !== defaultBranch ||
        pr.base?.repo?.full_name !== repository
      )
        continue;
      if (
        pr.number !== record.number ||
        pr.state !== "closed" ||
        record.pr.base_ref !== defaultBranch ||
        !Number.isFinite(Date.parse(pr.merged_at)) ||
        !isSha(pr.merge_commit_sha)
      )
        throw Error(`Invalid merged PR identity: ${record.number}`);
      admissions.push({
        ...record,
        merged_at: pr.merged_at,
        merge_commit_sha: pr.merge_commit_sha,
      });
    }
  } else {
    const path = join(root, cachePath);
    admissions = existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : [];
  }
  if (!Array.isArray(admissions)) throw Error("Invalid admission cache");
  // Retain every eligible receipt so later rebuilds preserve first verification.
  admissions = eligibleAdmissions(admissions).filter(
    (record) => submissions.has(record.result_id) && sourceTree(root, record),
  );
  const catalogue = generateCatalogue({
    legacy,
    admissions,
    metadataById: new Map(
      [...submissions].filter(([id]) => !legacyIds.has(id)),
    ),
  });
  if (online) {
    const published = new Set(
      [...catalogue.records, ...(catalogue.historical_records || [])].map(
        proofRevision,
      ),
    );
    for (const id of submissions.keys())
      if (!published.has(id))
        throw Error(`Submission has no verified publication record: ${id}`);
  }
  const selected = selectedAdmissions(admissions);
  const newCertificates = new Map();
  for (const record of catalogueProofRecords(catalogue)) {
    if (record.status !== "framework-verified") continue;
    const id = proofRevision(record);
    if (record.certificate_url !== `certificates/${id}.json`)
      throw Error(`Invalid verification record path: ${id}`);
    const evidence = legacyIds.has(id)
      ? historicalCertificate(submissions.get(id))
      : selected.find(
          ({ admission, verification }) =>
            admission.result_id === record.id &&
            admission.head_sha === record.source_commit &&
            verification.certificate.verified_at === record.first_verified_at,
        )?.verification.certificate;
    if (!evidence) throw Error(`Missing admitted certificate: ${record.id}`);
    const path = join(root, "public", record.certificate_url);
    if (existsSync(path)) {
      const previous = certificate(JSON.parse(readFileSync(path, "utf8")));
      // Permit migration from a previously published rerun only if that exact
      // certificate is also authenticated for this source. Forgery still fails.
      if (
        !isDeepStrictEqual(previous, evidence) &&
        !admissions.some(
          (admission) =>
            admission.result_id === record.id &&
            admission.head_sha === record.source_commit &&
            isDeepStrictEqual(admission.certificate, previous),
        )
      )
        throw Error(
          `Published certificate conflicts with admission: ${record.id}`,
        );
    }
    newCertificates.set(path, evidence);
  }
  // Validate every input before changing generated files or the offline cache.
  for (const [path, evidence] of newCertificates) {
    mkdirSync(join(root, "public/certificates"), { recursive: true });
    writeFileSync(path, json(evidence));
  }
  mkdirSync(join(root, "catalogue"), { recursive: true });
  writeFileSync(join(root, "catalogue/results.json"), json(catalogue));
  if (online) {
    mkdirSync(join(root, ".work"), { recursive: true });
    writeFileSync(join(root, cachePath), json(admissions));
  }
  return catalogue;
}

if (
  process.argv[1] &&
  import.meta.url === pathToFileURL(resolve(process.argv[1])).href
) {
  const online = process.argv.includes("--online");
  if (
    online &&
    process.env.GITHUB_REF !== `refs/heads/${process.env.QRH_DEFAULT_BRANCH}`
  )
    throw Error("Online reconciliation must use the default-branch checkout");
  const catalogue = await reconcileAdmissions({ online });
  console.log(
    `Generated catalogue: ${catalogue.records.length} results from proof metadata and admitted merges.`,
  );
}
