// Local preview only: read public PR metadata with gh; never execute candidate files.
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { rational } from "../core/rational.mjs";

const repo = JSON.parse(readFileSync("site.config.json", "utf8")).repository;
const api = (route) =>
  JSON.parse(execFileSync("gh", ["api", route], { encoding: "utf8" }));
const contents = (repository, file, ref) =>
  JSON.parse(
    Buffer.from(
      api(`repos/${repository}/contents/${file}?ref=${ref}`).content,
      "base64",
    ).toString(),
  );
const repository = api(`repos/${repo}`);
const base = contents(
  repo,
  "catalogue/results.json",
  repository.default_branch,
);
const known = new Map(base.records.map((r) => [r.id, r]));
const prs = JSON.parse(
  execFileSync(
    "gh",
    [
      "api",
      "--paginate",
      "--slurp",
      `repos/${repo}/pulls?state=open&per_page=100`,
    ],
    { encoding: "utf8" },
  ),
).flat();
const records = [];
for (const pr of prs) {
  const files = api(`repos/${repo}/pulls/${pr.number}/files?per_page=100`);
  const candidate = contents(
    pr.head.repo.full_name,
    "catalogue/results.json",
    pr.head.sha,
  );
  const additions = candidate.records.filter(
    (r) =>
      files.some((f) => f.filename === "catalogue/results.json") &&
      (!known.has(r.id) ||
        JSON.stringify(r.theta) !== JSON.stringify(known.get(r.id).theta)),
  );
  for (const r of additions) {
    rational(r.theta.numerator, r.theta.denominator);
    records.push({
      id: r.id,
      pr: pr.number,
      head_sha: pr.head.sha,
      head_repository: pr.head.repo.full_name,
      title: r.title,
      authors: r.authors,
      theta: r.theta,
      exact_bound: r.exact_bound,
      method: r.method,
      entrypoint: r.entrypoint,
      license: r.license,
      references: r.references,
      builds_on: r.builds_on,
      submitted_at: pr.created_at,
      state: "manual-review",
      run_url: null,
    });
  }
  // Existing proposal PRs can be previewed using their explicitly stated rational claim.
  // They remain proposals, never catalogue or verified entries.
  if (!additions.length && /proposal|retuning/i.test(pr.title)) {
    const match = /`(\d+)\s*\/\s*(\d+)`/.exec(pr.body);
    if (match) {
      rational(match[1], match[2]);
      records.push({
        id: `proposal-pr-${pr.number}`,
        pr: pr.number,
        head_sha: pr.head.sha,
        head_repository: pr.head.repo.full_name,
        title: pr.title,
        authors: [{ name: pr.user.login }],
        theta: { numerator: match[1], denominator: match[2] },
        method:
          "Exact retuning proposal with a standalone arithmetic certificate; full-cohort elaboration and independent kernel replay remain pending.",
        submitted_at: pr.created_at,
        state: "manual-review",
        run_url: null,
        proposal: true,
      });
    }
  }
}
writeFileSync(
  "dist/preview-submissions.json",
  JSON.stringify(
    {
      schema_version: 1,
      repository: repo,
      snapshot_at: new Date().toISOString(),
      records,
    },
    null,
    2,
  ) + "\n",
);
console.log(
  `Preview snapshot: ${records.length} pending entries from open PRs ${records.map((r) => "#" + r.pr).join(", ")}. No repository data published.`,
);
