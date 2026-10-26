// Fetch immutable Git objects; never check out or execute the submitted project.
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { exactBound } from "../../core/exact-bound.mjs";
const c = JSON.parse(readFileSync("verification-context/context.json", "utf8"));
const e = c.expected;
mkdirSync("verification", { recursive: true });
const result = (status, reason) =>
  writeFileSync(
    "verification/attempt.json",
    JSON.stringify({ ...e, status, reason }, null, 2) + "\n",
  );
result("infrastructure-blocked", "Worker setup did not complete");
if (
  !/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(e.repository) ||
  !/^[a-f0-9]{40}$/.test(e.head_sha) ||
  !/^[a-z][a-z0-9-]{2,63}$/.test(e.result_id)
)
  throw Error("Invalid verification identity");
try {
  exactBound(e.theta_exact);
} catch (error) {
  result("infrastructure-blocked", error.message);
  console.error(error.message);
  process.exit(1);
}
const env = {
  PATH: process.env.PATH,
  HOME: process.env.RUNNER_TEMP || process.env.HOME,
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_TERMINAL_PROMPT: "0",
};
// The trusted source fetch must use the isolated worker's egress proxy.
for (const name of [
  "HTTPS_PROXY",
  "https_proxy",
  "HTTP_PROXY",
  "http_proxy",
  "NO_PROXY",
  "no_proxy",
])
  if (process.env[name] !== undefined) env[name] = process.env[name];
const git = (args) =>
  execFileSync("git", ["-c", "core.hooksPath=/dev/null", ...args], {
    env,
    stdio: "pipe",
    timeout: 300_000,
    maxBuffer: 12 * 1024 ** 2,
  });
git(["init", "--bare", "verification/source.git"]);
git([
  "-C",
  "verification/source.git",
  "fetch",
  "--depth=1",
  "--no-tags",
  `https://github.com/${e.repository}.git`,
  e.head_sha,
]);
try {
  const listing = git([
    "-C",
    "verification/source.git",
    "ls-tree",
    e.head_sha,
    "--",
    `submissions/${e.result_id}/src/Candidate/Main.lean`,
  ]).toString();
  if (!listing)
    throw new Error(
      `Add submissions/${e.result_id}/src/Candidate/Main.lean with theorem Candidate.bound`,
    );
  // Preparation binds source and generates the theorem before provisioning libraries.
  writeFileSync("verification/empty-libraries.json", "{}\n");
  execFileSync(
    process.execPath,
    [
      "verifier/standard/prepare.mjs",
      "--checkout",
      "verification/source.git",
      "--head",
      e.head_sha,
      "--repository",
      e.repository,
      "--id",
      e.result_id,
      "--bound",
      e.theta_exact,
      "--libraries",
      "verification/empty-libraries.json",
      "--out",
      "verification/prepared",
    ],
    { env, stdio: "pipe" },
  );
  const contract = JSON.parse(
    readFileSync("verification/prepared/contract.json", "utf8"),
  );
  // All proof modules come from the prepared submission dependency graph.
  writeFileSync(
    "verification/imports.json",
    JSON.stringify(contract.package_imports) + "\n",
  );
  console.log(`Prepared ${contract.manifest.id} at ${e.head_sha}`);
} catch (error) {
  const detail = error.stderr?.toString() || error.message;
  result("invalid-submission", detail.slice(-4000));
  console.error(detail);
  process.exitCode = 1;
}
