import { mkdirSync, writeFileSync } from "node:fs";
import path from "node:path";
import { safePath, submission } from "./manifest.mjs";
import { sha256 } from "./common.mjs";
export async function api(route, token = process.env.GITHUB_TOKEN) {
  const response = await fetch("https://api.github.com/" + route, {
    headers: {
      Accept: "application/vnd.github+json",
      "X-GitHub-Api-Version": "2022-11-28",
      Authorization: `Bearer ${token}`,
    },
  });
  if (!response.ok) throw Error(`GitHub API ${response.status} for ${route}`);
  return response.json();
}
export async function pages(route) {
  let result = [];
  for (let page = 1; page <= 100; page++) {
    const rows = await api(
      `${route}${route.includes("?") ? "&" : "?"}per_page=100&page=${page}`,
    );
    if (!Array.isArray(rows)) throw Error("Unexpected GitHub response");
    result.push(...rows);
    if (rows.length < 100) return result;
  }
  throw Error("GitHub pagination limit exceeded");
}
export function allowedChanges(files) {
  if (!files.length || files.length > 260) throw Error("Invalid PR size");
  let id = null;
  for (const f of files) {
    const name = safePath(f.filename);
    const m = /^submissions\/([a-z][a-z0-9-]{2,63})\/(.+)$/.exec(name);
    if (!m || f.status === "renamed" || f.status === "removed")
      throw Error(
        "Submission PRs may change only one submission, without renames or deletions",
      );
    if (id && id !== m[1]) throw Error("Only one submission per PR");
    id = m[1];
    if (
      !["manifest.json", "explanation.md", "LICENSE", "NOTICE"].includes(
        m[2],
      ) &&
      !/^src\/Candidate\/(?:[A-Z][A-Za-z0-9_]*\/)*[A-Z][A-Za-z0-9_]*\.lean$/.test(
        m[2],
      )
    )
      throw Error("Unapproved candidate file");
  }
  return id;
}
export async function inspectPR(repo, number) {
  if (
    !/^[\w.-]+\/[\w.-]+$/.test(repo) ||
    !Number.isSafeInteger(number) ||
    number < 1
  )
    throw Error("Invalid PR identity");
  const p = await api(`repos/${repo}/pulls/${number}`);
  const files = await pages(`repos/${repo}/pulls/${number}/files`);
  const id = allowedChanges(files);
  if (p.base.repo.full_name !== repo) throw Error("Wrong PR base");
  return {
    id,
    base_repository: repo,
    head_repository: p.head.repo.full_name,
    head_sha: p.head.sha,
    author: p.user.login,
    is_draft: p.draft,
    state: p.state,
    submitted_at: p.created_at,
    merged_at: p.merged_at,
    merge_commit: p.merge_commit_sha,
    number,
  };
}
export async function materialize(repo, commit, id, dest) {
  if (!/^[a-f0-9]{40}$/.test(commit) || !/^([a-z][a-z0-9-]{2,63})$/.test(id))
    throw Error("Invalid source identity");
  const tree = await api(`repos/${repo}/git/trees/${commit}?recursive=1`);
  if (tree.truncated) throw Error("Truncated tree refused");
  const prefix = `submissions/${id}/`;
  const entries = tree.tree.filter(
    (e) => e.path.startsWith(prefix) && e.type !== "tree",
  );
  let bytes = 0;
  for (const e of entries) {
    const rel = safePath(e.path.slice(prefix.length));
    if (e.mode !== "100644" && e.mode !== "100755")
      throw Error("Symlinks/submodules not allowed");
    if (e.type !== "blob" || e.size > 2 * 1024 * 1024)
      throw Error("Invalid source blob");
    bytes += e.size;
    if (bytes > 10 * 1024 * 1024 || entries.length > 256)
      throw Error("Submission size limit");
    const blob = await api(`repos/${repo}/git/blobs/${e.sha}`);
    if (blob.encoding !== "base64") throw Error("Unexpected blob");
    const data = Buffer.from(blob.content, "base64");
    if (data.length !== e.size) throw Error("Blob size mismatch");
    const full = path.join(dest, rel);
    mkdirSync(path.dirname(full), { recursive: true });
    writeFileSync(full, data, { mode: 0o444 });
  }
  const result = submission(dest);
  if (result.manifest.id !== id)
    throw Error("Manifest ID does not match directory");
  return result;
}
export async function reviews(repo, n) {
  return (await pages(`repos/${repo}/pulls/${n}/reviews`)).map((r) => ({
    id: r.id,
    login: r.user.login,
    state: r.state,
    commit_id: r.commit_id,
    submitted_at: r.submitted_at ?? "",
  }));
}
