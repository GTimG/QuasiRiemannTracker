// Run from a trusted checkout. Read submission Git blobs as data.
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync, rmSync } from "node:fs";
import { resolve, dirname, join } from "node:path";
import { parseArgs } from "node:util";
import { exactBound } from "../../core/exact-bound.mjs";
import { submission, safePath } from "../manifest.mjs";
import { challenge, solutionWrapper } from "../challenge.mjs";
import { leanImports } from "../actions/imports.mjs";
import { dependencyGraph } from "../submission-dependencies.mjs";
import { sha256 } from "../common.mjs";
const { values: v } = parseArgs({
  options: Object.fromEntries(
    [
      "checkout",
      "head",
      "repository",
      "id",
      "libraries",
      "bound",
      "source-commit",
      "out",
    ].map((k) => [k, { type: "string" }]),
  ),
});
if (
  !/^[a-f0-9]{40}$/.test(v.head ?? "") ||
  !/^[\w.-]+\/[\w.-]+$/.test(v.repository ?? "") ||
  !/^[a-z][a-z0-9-]{2,63}$/.test(v.id ?? "")
)
  throw Error("Invalid source identity");
const out = resolve(v.out);
mkdirSync(out);
const source = join(out, "submission");
mkdirSync(source);
const git = (args) =>
  execFileSync("git", ["-C", resolve(v.checkout), ...args], {
    maxBuffer: 128 * 1024 * 1024,
  });
const sourceCommit = v["source-commit"] ?? v.head;
if (!/^[a-f0-9]{40}$/.test(sourceCommit))
  throw Error("Invalid original source commit");
const trees = {};
let total = 0,
  fileCount = 0;
const graph = dependencyGraph(v.id, (id) => {
  const prefix = `submissions/${id}/`;
  const entries = git(["ls-tree", "-rz", v.head, "--", prefix]).toString();
  const rows = entries.split("\0").filter(Boolean);
  fileCount += rows.length;
  if (fileCount > 16384) throw Error("Submission dependency file count limit");
  if (!rows.length || rows.length > 8192)
    throw Error(`Invalid submission file count: ${id}`);
  if (
    entries !== git(["ls-tree", "-rz", sourceCommit, "--", prefix]).toString()
  )
    throw Error(
      `Original dependency source differs from the reviewed head: ${id}`,
    );
  trees[id] = git(["rev-parse", `${v.head}:submissions/${id}`])
    .toString()
    .trim();
  const dir = join(out, "inputs", id);
  mkdirSync(dir, { recursive: true });
  for (const row of rows) {
    const match = /^(100644|100755) blob ([a-f0-9]{40})\t(.+)$/.exec(row);
    if (!match) throw Error("Submission requires regular Git files");
    const name = safePath(match[3].slice(prefix.length));
    const bytes = git(["cat-file", "blob", match[2]]);
    total += bytes.length;
    if (total > 128 * 1024 * 1024)
      throw Error("Submission dependency source size limit");
    const file = join(dir, name);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, bytes, { mode: 0o444 });
  }
  return submission(dir, { id, ...exactBound(v.bound) });
});
const s = graph.submissions.get(v.id);
const sourceFiles = {};
function stage(name, bytes) {
  if (sourceFiles[name]) throw Error(`Duplicate prepared source: ${name}`);
  const file = join(source, name);
  mkdirSync(dirname(file), { recursive: true });
  writeFileSync(file, bytes, { mode: 0o444 });
  sourceFiles[name] = sha256(bytes);
}
for (const [id, input] of graph.submissions) {
  const file = input.files.find((f) => f.path === "metadata.json");
  stage(
    id === v.id ? file.path : `dependencies/${id}/metadata.json`,
    file.bytes,
  );
}
for (const { file } of graph.modules.values()) stage(file.path, file.bytes);
rmSync(join(out, "inputs"), { recursive: true });
const order = graph.order;
const generated = {
  "Challenge.lean": challenge(s.manifest),
  "Solution.lean": solutionWrapper(s.manifest),
};
for (const [name, body] of Object.entries(generated))
  writeFileSync(join(out, name), body, { mode: 0o444 });
const libraries = readFileSync(v.libraries);
writeFileSync(join(out, "libraries.json"), libraries, { mode: 0o444 });
writeFileSync(
  join(out, "contract.json"),
  JSON.stringify(
    {
      schema_version: 2,
      repository: v.repository,
      head_sha: v.head,
      source_commit: sourceCommit,
      manifest: s.manifest,
      source_files: sourceFiles,
      submission_trees: trees,
      module_dependencies: graph.dependencies,
      package_imports: [
        ...new Set(
          order
            .flatMap((name) =>
              leanImports(graph.modules.get(name).file.bytes.toString()),
            )
            .filter((name) =>
              /^(PrimeNumberTheoremAnd|RellichKondrachov)(\.|$)/.test(name),
            ),
        ),
      ].sort(),
      build_order: order,
      generated_files: Object.fromEntries(
        Object.entries(generated).map(([k, b]) => [k, sha256(b)]),
      ),
      library_inventory_sha256: sha256(libraries),
    },
    null,
    2,
  ) + "\n",
  { mode: 0o444 },
);
console.log(
  `Prepared ${s.manifest.id} at ${v.head}: ${order.length} Lean modules`,
);
