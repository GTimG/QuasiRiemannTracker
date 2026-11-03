// Read publication facts from the current local archive tree. Inclusion is
// determined by checked-out submissions, never by the presence of a receipt.
import { execFileSync } from "node:child_process";
import { certificate } from "../verifier/certificate.mjs";
import { validSubmissionSourcePath } from "../verifier/submission-paths.mjs";

function git(root, args, options = {}) {
  return execFileSync("git", ["--no-replace-objects", ...args], {
    cwd: root,
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
    maxBuffer: 8 * 1024 * 1024,
    ...options,
  });
}

function archiveTip(root) {
  for (const ref of [
    "refs/remotes/origin/admission-records",
    "refs/heads/admission-records",
  ]) {
    try {
      return git(root, ["rev-parse", "--verify", `${ref}^{commit}`]).trim();
    } catch (error) {
      if (error.code !== "ENOENT" && ![1, 128].includes(error.status))
        throw error;
    }
  }
  return null;
}

export function readLocalPublications(root) {
  const tip = archiveTip(root);
  if (!tip) return {};
  const entries = git(root, ["ls-tree", "-rlz", tip, "--", "records/"])
    .split("\0")
    .filter(Boolean);
  const publications = Object.create(null);
  for (const entry of entries) {
    const match =
      /^100644 blob ([a-f0-9]{40})\s+(\d+)\t(records\/.+\.json)$/.exec(entry);
    if (!match || Number(match[2]) > 8 * 1024 * 1024)
      throw Error("Invalid local publication data file");
    const record = JSON.parse(git(root, ["cat-file", "blob", match[1]]));
    const evidence = certificate(record.certificate);
    if (
      evidence.result_id !== record.result_id ||
      !validSubmissionSourcePath(record.source_path, record.result_id) ||
      !Number.isSafeInteger(record.number) ||
      record.number <= 0 ||
      !Number.isFinite(Date.parse(record.pr?.created_at))
    )
      throw Error("Invalid local publication facts");
    const facts = {
      pr: record.number,
      submitted_at: record.pr.created_at,
      source_path: record.source_path,
      certificate: evidence,
    };
    (publications[record.result_id] ??= []).push(facts);
  }
  // Reruns may add reports without changing the statement. Retain the earliest
  // recorded check for each exact bound; the builder selects its current bound.
  for (const facts of Object.values(publications))
    facts.sort(
      (a, b) =>
        Date.parse(a.certificate.verified_at) -
          Date.parse(b.certificate.verified_at) ||
        a.certificate.source_commit.localeCompare(
          b.certificate.source_commit,
        ) ||
        a.pr - b.pr,
    );
  return publications;
}
