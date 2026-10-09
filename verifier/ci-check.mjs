import { mkdirSync, writeFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { readJSON, sha256 } from "./common.mjs";
import { inspectPR, materialize } from "./github.mjs";
import { check } from "./runner.mjs";
const policy = readJSON("verifier/trust-policy.json"),
  repo = process.env.GITHUB_REPOSITORY,
  pr = Number(process.env.QRH_PR),
  rev = process.env.GITHUB_WORKFLOW_SHA;
if (
  repo !== policy.repository ||
  process.env.GITHUB_REF !== `refs/heads/${process.env.QRH_DEFAULT_BRANCH}` ||
  !/^[a-f0-9]{40}$/.test(rev ?? "")
)
  throw Error("Trusted default-branch orchestration required");
const source = await inspectPR(repo, pr);
if (source.is_draft) throw Error("Draft submission");
const dir = mkdtempSync(path.join(tmpdir(), "qrh-source-"));
mkdirSync("out", { recursive: true });
try {
  await materialize(source.head_repository, source.head_sha, source.id, dir);
  const result = await check(dir, {
    image: policy.worker_image,
    sourceCommit: source.head_sha,
    repository: repo,
    pr,
    orchestratorCommit: rev,
  });
  const { log, ...attempt } = result;
  writeFileSync("out/attempt.json", JSON.stringify(attempt, null, 2) + "\n");
  writeFileSync("out/verification.log", log);
  writeFileSync("out/source.json", JSON.stringify(source, null, 2) + "\n");
  if (result.status !== "accepted") {
    console.error(result.status);
    process.exitCode = result.status === "infrastructure-blocked" ? 78 : 1;
  }
} finally {
  rmSync(dir, { recursive: true, force: true });
}
