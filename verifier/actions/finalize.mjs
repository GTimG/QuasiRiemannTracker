// Runs in the publishing job, using only base-branch code and same-run artifacts.
import {
  readFileSync,
  existsSync,
  writeFileSync,
  mkdirSync,
  readdirSync,
} from "node:fs";
import { join } from "node:path";
import { api } from "../github-api.mjs";
import { parseDeclaration } from "../pr-admission.mjs";
import { validateDecimalApproximation } from "../pr-decimal.mjs";
import { verificationResult } from "./result.mjs";
import { workerCertificate } from "../certificate.mjs";
import { archiveAdmission } from "../admission-archive.mjs";
import { readSubmissionSources } from "../submission-metadata.mjs";
import { validatePublication } from "../publication-record.mjs";
const c = JSON.parse(readFileSync("verification-context/context.json", "utf8"));
const attemptNumber = (value) =>
  /^[1-9][0-9]{0,5}$/.test(value ?? "") ? Number(value) : NaN;
const currentAttempt = attemptNumber(process.env.GITHUB_RUN_ATTEMPT);
const contextAttempt = attemptNumber(c.run_attempt);
// "Re-run failed jobs" reuses the context written by the attempt in which the
// prepare job last ran, so the context may predate the current attempt.
if (
  c.repository !== process.env.GITHUB_REPOSITORY ||
  c.run_id !== process.env.GITHUB_RUN_ID ||
  c.run_attempt !== process.env.QRH_CONTEXT_ATTEMPT ||
  !(contextAttempt <= currentAttempt) ||
  c.workflow_sha !== process.env.GITHUB_WORKFLOW_SHA ||
  process.env.GITHUB_REF !== `refs/heads/${c.defaultBranch}`
)
  throw Error(
    "Verification context does not belong to this protected workflow run",
  );
// Matrix legs that passed are not repeated by "Re-run failed jobs", so results
// can come from different attempts. Use the newest attempt for each result
// among those that ran against this context.
function workerAttempt(resultId) {
  const root = "verification-results";
  const attempts = (existsSync(root) ? readdirSync(root) : []).flatMap(
    (name) => {
      const match = /^proof-verification-([1-9][0-9]*)-(.+)$/.exec(name);
      const n = match ? attemptNumber(match[1]) : NaN;
      return match?.[2] === resultId &&
        n >= contextAttempt &&
        n <= currentAttempt
        ? [n]
        : [];
    },
  );
  return attempts.length ? Math.max(...attempts) : currentAttempt;
}
let conclusion = "failure",
  summary;
try {
  const p = await api(`repos/${c.repository}/pulls/${c.expected.number}`);
  const identity = (p) =>
    JSON.stringify([
      p.state,
      p.head.sha,
      p.base.sha,
      p.base.ref,
      p.base.repo.full_name,
      p.body,
      p.changed_files,
    ]);
  if (identity(p) !== identity(c.pr))
    throw Error(
      "PR head, base or declaration changed during verification; rerun admission",
    );
  const declaration = parseDeclaration(p.body);
  const sources = declaration
    ? await readSubmissionSources(api, {
        repository: c.repository,
        head_sha: p.head.sha,
        result_id: declaration.result_id,
      })
    : null;
  const metadata = sources?.metadata;
  const catalogue = declaration
    ? JSON.parse(readFileSync("verification-context/catalogue.json", "utf8"))
    : null;
  const expectations = c.expectations;
  if (!Array.isArray(expectations) || !expectations.length)
    throw Error("Verification context has no proof targets");
  if (declaration && expectations.length !== 1)
    throw Error("A new-bound declaration must have exactly one proof target");
  const summaries = [];
  mkdirSync("verification/certificates", { recursive: true });
  for (const expected of expectations) {
    const worker = workerAttempt(expected.result_id);
    const directory = `verification-results/proof-verification-${worker}-${expected.result_id}`;
    const attemptPath = join(directory, "attempt.json");
    const attempt = existsSync(attemptPath)
      ? JSON.parse(readFileSync(attemptPath, "utf8"))
      : null;
    const completion = existsSync(join(directory, "worker-status.json"))
      ? JSON.parse(readFileSync(join(directory, "worker-status.json"), "utf8"))
          .result
      : "failure";
    const report = verificationResult(
      process.cwd(),
      expected,
      attempt,
      completion,
    );
    if (declaration)
      validateDecimalApproximation({
        ...declaration,
        catalogue,
      });
    const record =
      attempt.status === "accepted"
        ? workerCertificate(
            expected,
            report,
            `https://github.com/${c.repository}/actions/runs/${c.run_id}/attempts/${worker}`,
            readFileSync(join(directory, "run/result.json")),
          )
        : report;
    if (declaration)
      validatePublication(catalogue, {
        ...expected,
        metadata,
        certificate: record,
        source_path: sources.source_path,
        pr: p,
      });
    writeFileSync(
      `verification/certificates/${expected.result_id}.json`,
      JSON.stringify(record, null, 2) + "\n",
    );
    if (declaration)
      await archiveAdmission({
        // Archive under the attempt whose worker produced the report.
        context: { ...c, run_attempt: String(worker) },
        pr: p,
        expected,
        record,
        metadata,
        reportBytes:
          attempt.status === "accepted"
            ? readFileSync(join(directory, "run/result.json"))
            : null,
      });
    summaries.push(
      `Proof verification accepts ${expected.result_id} at ${expected.theta_exact} for this exact PR head.`,
    );
    if (attempt.status === "registered")
      summaries.push(
        "A protected independently verified receipt was authenticated against this exact source and current verifier policy; no proof replay was needed.",
      );
    else if (attempt.status !== "accepted")
      summaries.push(
        "A matching independently verified local run supplied the result because hosted verification was unavailable.",
      );
  }
  if (
    identity(await api(`repos/${c.repository}/pulls/${c.expected.number}`)) !==
    identity(c.pr)
  )
    throw Error("PR changed while archiving verification; rerun admission");
  conclusion = "success";
  summary = summaries.join(" ");
  if (declaration)
    summary += ` Decimal ${declaration.theta_decimal} accurately approximates the exact bound.`;
  else summary = `Maintenance validations passed. ${summary}`;
} catch (error) {
  summary = `Admission failed: ${error.message}`;
  process.exitCode = 1;
}
const response = await fetch(
  `https://api.github.com/repos/${c.repository}/check-runs/${c.check_id}`,
  {
    method: "PATCH",
    headers: {
      Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
      "Content-Type": "application/json",
      Accept: "application/vnd.github+json",
    },
    body: JSON.stringify({
      status: "completed",
      conclusion,
      completed_at: new Date().toISOString(),
      output: {
        title:
          conclusion === "success"
            ? "PR admission requirements satisfied"
            : "PR admission failed",
        summary,
      },
    }),
  },
);
if (!response.ok)
  throw Error(`Publishing admission failed: HTTP ${response.status}`);
console.log(summary);
