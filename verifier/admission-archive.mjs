// Only the trusted admission publisher writes this ref. It contains data, never
// executable candidate code, and is independent of Actions artifact retention.
import { certificate } from "./certificate.mjs";
import { canonical, sha256 } from "./common.mjs";
import { parseDeclaration } from "./pr-admission.mjs";
import { verificationResult } from "./actions/result.mjs";
import {
  parseSubmissionMetadata,
  readSubmissionSources,
  validateSubmissionMetadata,
} from "./submission-metadata.mjs";

export const ADMISSION_BRANCH = "admission-records";
const sha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");
const repository = (value) => /^[\w.-]+\/[\w.-]+$/.test(value ?? "");
const positive = (value) => Number.isSafeInteger(value) && value > 0;
const runNumber = (value) => /^[1-9][0-9]*$/.test(String(value ?? ""));
const maxRecordBytes = 8 * 1024 * 1024;
const authorUrl = (login) =>
  login.endsWith("[bot]")
    ? `https://github.com/apps/${login.slice(0, -5)}`
    : `https://github.com/${login}`;

function validateIdentity(record) {
  if (
    !positive(record?.number) ||
    !sha(record.head_sha) ||
    !/^[a-z][a-z0-9-]{2,63}$/.test(record.result_id ?? "")
  )
    throw Error("Invalid admission archive identity");
}

export function admissionPath(record) {
  validateIdentity(record);
  validateSubmissionMetadata(record.metadata);
  if (
    !runNumber(record.admission?.run_id) ||
    !runNumber(record.admission.run_attempt)
  )
    throw Error("Invalid admission archive attempt identity");
  return `records/${record.number}/${record.head_sha}/${record.result_id}/${record.admission.run_id}-${record.admission.run_attempt}.json`;
}

export function validateAdmissionRecord(value) {
  admissionPath(value);
  const c = certificate(value.certificate);
  const p = value.pr;
  const a = value.admission;
  if (
    ![1, 2].includes(value.schema_version) ||
    !repository(value.repository) ||
    value.source_path !== `submissions/${value.result_id}/src` ||
    !sha(value.source_tree) ||
    c.source_repository !== value.repository ||
    c.source_commit !== value.head_sha ||
    c.result_id !== value.result_id ||
    c.theta_exact !== value.theta_exact ||
    p?.number !== value.number ||
    typeof p.title !== "string" ||
    !p.title.trim() ||
    p.title.length > 1024 ||
    typeof p.body !== "string" ||
    p.body.length > 65536 ||
    !Number.isFinite(Date.parse(p.created_at)) ||
    !/^[a-zA-Z0-9][a-zA-Z0-9-]{0,99}(?:\[bot\])?$/.test(
      p.author?.login ?? "",
    ) ||
    p.author.url !== authorUrl(p.author.login) ||
    typeof p.base_ref !== "string" ||
    !p.base_ref ||
    !runNumber(a?.run_id) ||
    !runNumber(a.run_attempt) ||
    !sha(a.workflow_sha) ||
    !positive(a.check_id) ||
    !Number.isFinite(Date.parse(a.archived_at))
  )
    throw Error("Invalid admission archive record");
  const declaration = parseDeclaration(p.body);
  if (
    declaration?.result_id !== value.result_id ||
    declaration.theta_exact !== value.theta_exact
  )
    throw Error("Archived PR declaration differs from its verified result");
  if (
    value.schema_version === 1 &&
    canonical(value.metadata) !== canonical(parseSubmissionMetadata(p.body))
  )
    throw Error("Archived metadata differs from the verified PR body");
  if (
    value.schema_version === 2 &&
    value.metadata_sha256 !== sha256(canonical(value.metadata))
  )
    throw Error("Archived metadata differs from the verified source metadata");
  const dependencyTrees = value.dependency_trees ?? {};
  if (
    typeof dependencyTrees !== "object" ||
    Array.isArray(dependencyTrees) ||
    Object.entries(dependencyTrees).some(
      ([id, tree]) => !/^[a-z][a-z0-9-]{2,63}$/.test(id) || !sha(tree),
    ) ||
    (value.metadata.dependencies ?? []).some(
      (id) => !Object.hasOwn(dependencyTrees, id),
    )
  )
    throw Error("Admission is missing immutable dependency trees");
  if (value.report_json !== null) {
    if (
      typeof value.report_json !== "string" ||
      sha256(value.report_json) !== c.report_sha256 ||
      c.report_url !==
        `https://github.com/${value.repository}/actions/runs/${a.run_id}/attempts/${a.run_attempt}`
    )
      throw Error("Archived report differs from its verification certificate");
    const expected = {
      repository: value.repository,
      number: value.number,
      head_sha: value.head_sha,
      result_id: value.result_id,
      theta_exact: value.theta_exact,
    };
    const report = JSON.parse(value.report_json);
    verificationResult("", expected, {
      ...expected,
      status: "accepted",
      report,
    });
    if (
      report.verified_at !== c.verified_at ||
      canonical(report.bound_interval ?? null) !==
        canonical(c.bound_interval ?? null)
    )
      throw Error("Archived report metadata differs from its certificate");
  }
  if (Buffer.byteLength(JSON.stringify(value)) > maxRecordBytes)
    throw Error("Admission archive record is too large");
  return value;
}

export function admissionRecord({
  context,
  pr,
  expected,
  record,
  sourceTree,
  dependencyTrees = {},
  metadata,
  reportBytes = null,
  archivedAt = new Date().toISOString(),
}) {
  if (
    context.repository !== expected.repository ||
    pr.number !== expected.number ||
    pr.state !== "open" ||
    pr.head.sha !== expected.head_sha ||
    pr.base.ref !== context.defaultBranch ||
    pr.base.repo.full_name !== expected.repository
  )
    throw Error("Admission archive requires the current verified PR identity");
  return validateAdmissionRecord({
    schema_version: 2,
    ...Object.fromEntries(
      ["repository", "number", "head_sha", "result_id", "theta_exact"].map(
        (key) => [key, expected[key]],
      ),
    ),
    source_path: `submissions/${expected.result_id}/src`,
    source_tree: sourceTree,
    dependency_trees: dependencyTrees,
    metadata: structuredClone(validateSubmissionMetadata(metadata)),
    metadata_sha256: sha256(canonical(metadata)),
    certificate: record,
    report_json: reportBytes === null ? null : reportBytes.toString("utf8"),
    pr: {
      number: pr.number,
      title: pr.title,
      body: pr.body,
      created_at: pr.created_at,
      author: {
        login: pr.user?.login,
        url: authorUrl(pr.user?.login ?? ""),
      },
      base_ref: pr.base.ref,
    },
    admission: {
      run_id: String(context.run_id),
      run_attempt: String(context.run_attempt),
      workflow_sha: context.workflow_sha,
      check_id: context.check_id,
      archived_at: archivedAt,
    },
  });
}

function github(fetcher, token, repo) {
  return async (route, { method = "GET", body, allow = [] } = {}) => {
    let response;
    try {
      response = await fetcher(
        `https://api.github.com/repos/${repo}/${route}`,
        {
          method,
          headers: {
            Accept: "application/vnd.github+json",
            "Content-Type": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
            Authorization: `Bearer ${token}`,
          },
          ...(body ? { body: JSON.stringify(body) } : {}),
        },
      );
    } catch {
      throw Error("GitHub admission archive request failed");
    }
    if (allow.includes(response.status)) return { status: response.status };
    if (!response.ok)
      throw Error(
        `GitHub admission archive request failed: HTTP ${response.status}`,
      );
    try {
      return { status: response.status, data: await response.json() };
    } catch {
      throw Error("GitHub admission archive returned invalid JSON");
    }
  };
}

// Read only the exact commit's tree; candidate paths are never executed or
// extracted. Each response is shallow, avoiding recursive-tree truncation.
async function submissionTree(request, expected) {
  validateIdentity(expected);
  let treeSha = expected.head_sha;
  for (const part of ["submissions", expected.result_id, "src"]) {
    const { data } = await request(`git/trees/${treeSha}`);
    if (data?.truncated || !Array.isArray(data?.tree))
      throw Error("Incomplete admitted source tree");
    const entries = data.tree.filter((entry) => entry.path === part);
    if (
      entries.length !== 1 ||
      entries[0].type !== "tree" ||
      entries[0].mode !== "040000" ||
      !sha(entries[0].sha)
    )
      throw Error("Verified submission source tree is missing");
    treeSha = entries[0].sha;
  }
  return treeSha;
}

// Non-force ref updates provide compare-and-swap: a competing commit makes our
// sibling commit a non-fast-forward update, so retry against the new parent.
export async function archiveAdmission(
  input,
  { fetcher = fetch, token = process.env.GITHUB_TOKEN, attempts = 8 } = {},
) {
  if (!repository(input.expected?.repository) || !token)
    throw Error("Admission archive requires repository credentials");
  const request = github(fetcher, token, input.expected.repository);
  const sourceTree = await submissionTree(request, input.expected);
  const dependencyTrees = input.metadata.dependencies?.length
    ? (
        await readSubmissionSources(
          async (route) =>
            (
              await request(
                route.replace(`repos/${input.expected.repository}/`, ""),
              )
            ).data,
          input.expected,
        )
      ).trees
    : {};
  const envelope = admissionRecord({ ...input, sourceTree, dependencyTrees });
  const path = admissionPath(envelope);
  const content = JSON.stringify(envelope, null, 2) + "\n";
  let blobSha;
  for (let retry = 0; retry < attempts; retry++) {
    const ref = await request(`git/ref/heads/${ADMISSION_BRANCH}`, {
      allow: [404],
    });
    const parent = ref.status === 404 ? null : ref.data?.object?.sha;
    if (parent !== null && !sha(parent))
      throw Error("Invalid admission archive ref");
    let baseTree;
    if (parent) {
      const existing = await request(`contents/${path}?ref=${parent}`, {
        allow: [404],
      });
      if (existing.status !== 404) {
        if (
          existing.data?.type !== "file" ||
          existing.data.size > maxRecordBytes
        )
          throw Error("Invalid existing admission archive entry");
        // Contents omits inline data above 1 MiB. The immutable Git Blob API
        // still provides base64 bytes for records up to our explicit limit.
        let file = existing.data;
        if (file.encoding === "none" && sha(file.sha))
          file = (await request(`git/blobs/${file.sha}`)).data;
        if (
          file?.encoding !== "base64" ||
          file.size > maxRecordBytes ||
          typeof file.content !== "string"
        )
          throw Error("Invalid existing admission archive content");
        const saved = validateAdmissionRecord(
          JSON.parse(Buffer.from(file.content, "base64").toString("utf8")),
        );
        if (
          [
            "repository",
            "number",
            "head_sha",
            "result_id",
            "theta_exact",
            "source_path",
            "source_tree",
          ].some((key) => saved[key] !== envelope[key]) ||
          canonical(saved.dependency_trees ?? {}) !==
            canonical(envelope.dependency_trees ?? {}) ||
          canonical(saved.metadata) !== canonical(envelope.metadata) ||
          saved.admission.run_id !== envelope.admission.run_id ||
          saved.admission.run_attempt !== envelope.admission.run_attempt
        )
          throw Error(
            "Admission archive identity conflicts with an existing record",
          );
        return { commit: parent, path, record: saved };
      }
      const commit = await request(`git/commits/${parent}`);
      baseTree = commit.data?.tree?.sha;
      if (!sha(baseTree)) throw Error("Invalid admission archive tree");
    }
    if (!blobSha) {
      const blob = await request("git/blobs", {
        method: "POST",
        body: { content, encoding: "utf-8" },
      });
      blobSha = blob.data?.sha;
      if (!sha(blobSha)) throw Error("Invalid admission archive blob");
    }
    const tree = await request("git/trees", {
      method: "POST",
      body: {
        ...(baseTree ? { base_tree: baseTree } : {}),
        tree: [{ path, mode: "100644", type: "blob", sha: blobSha }],
      },
    });
    if (!sha(tree.data?.sha)) throw Error("Invalid new admission archive tree");
    const commit = await request("git/commits", {
      method: "POST",
      body: {
        message: `Archive verified PR #${envelope.number}: ${envelope.result_id}`,
        tree: tree.data.sha,
        parents: parent ? [parent] : [],
      },
    });
    if (!sha(commit.data?.sha))
      throw Error("Invalid new admission archive commit");
    const update = parent
      ? await request(`git/refs/heads/${ADMISSION_BRANCH}`, {
          method: "PATCH",
          body: { sha: commit.data.sha, force: false },
          allow: [409, 422],
        })
      : await request("git/refs", {
          method: "POST",
          body: {
            ref: `refs/heads/${ADMISSION_BRANCH}`,
            sha: commit.data.sha,
          },
          allow: [409, 422],
        });
    if (![409, 422].includes(update.status))
      return { commit: commit.data.sha, path, record: envelope };
  }
  throw Error("Admission archive changed concurrently; retry admission");
}
