import { readdirSync, mkdirSync, writeFileSync } from "node:fs";
import { check, preflight } from "./runner.mjs";
import { sha256, PIN_DIGEST, iso } from "./common.mjs";
const image = process.argv[2];
mkdirSync("evidence/integration", { recursive: true });
const cases = [
  { id: "baseline", path: "submissions/openai-baseline", expect: "accepted" },
  ...readdirSync("tests/adversarial").map((id) => ({
    id,
    path: "tests/adversarial/" + id,
    expect: "not-accepted",
  })),
];
const results = [];
for (const c of cases) {
  const r = await check(c.path, { image });
  const { log, ...data } = r;
  writeFileSync(`evidence/integration/${c.id}.log`, log);
  writeFileSync(
    `evidence/integration/${c.id}.json`,
    JSON.stringify(data, null, 2),
  );
  results.push({
    id: c.id,
    status: r.status,
    log_sha256: sha256(log),
    expected: c.expect,
  });
  console.log(c.id + ": " + r.status);
  if (r.status === "infrastructure-blocked") break;
}
const completed =
  results.length === cases.length && results[0]?.status === "accepted";
// A timeout or checker crash never counts as a demonstrated mathematical rejection.
const adversarial =
  completed && results.slice(1).every((r) => r.status === "checking-failed");
const summary = {
  kind: "qrh-integration-attempt-v1",
  at: iso(),
  worker_image: image ?? null,
  pin_digest: PIN_DIGEST,
  baseline: results[0]?.status ?? "not-run",
  adversarial_suite: adversarial ? "passed" : "not-established",
  isolation: completed ? "passed" : "not-established",
  results,
  production_ready: false,
};
writeFileSync(
  "evidence/integration/summary.json",
  JSON.stringify(summary, null, 2) + "\n",
);
process.exitCode = adversarial
  ? 0
  : results[0]?.status === "infrastructure-blocked"
    ? 78
    : 1;
