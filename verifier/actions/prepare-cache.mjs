// Prepare the shared build of every merged submission on the default branch.
// Run from the trusted checkout of a main commit. Submission files are read as
// data with the same dependency graph that admission preparation uses.
import { execFileSync } from "node:child_process";
import {
  mkdirSync,
  mkdtempSync,
  readdirSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { leanImports } from "./imports.mjs";
import { submissionFiles } from "../manifest.mjs";
import { dependencyGraph } from "../submission-dependencies.mjs";
import { submissionDirectory, submissionId } from "../submission-paths.mjs";

const SHARED = /^Submissions(?:\.[A-Za-z_][A-Za-z0-9_]*)+$/;

// Union the reusable modules of every merged submission. Dependencies are
// staged under Submissions.<id>.*, and a module's cache key depends only on its
// source and dependencies, so later PRs reuse exactly these modules. Each PR's
// Candidate.* modules are private to it and are not cached.
export function mergeContracts(prepared) {
  const source_files = {},
    module_dependencies = {},
    build_order = [],
    package_imports = new Set();
  for (const { contract } of prepared) {
    for (const name of contract.package_imports ?? [])
      package_imports.add(name);
    const deps = contract.module_dependencies;
    for (const module of contract.build_order) {
      if (
        !SHARED.test(module) ||
        !deps[module].every((d) => d in module_dependencies)
      )
        continue;
      const path = `src/${module.replaceAll(".", "/")}.lean`;
      const sha = contract.source_files[path];
      if (!sha) throw Error(`Prepared source is missing: ${path}`);
      if (!(path in source_files)) {
        source_files[path] = sha;
        module_dependencies[module] = [...deps[module]];
        build_order.push(module);
      } else if (
        source_files[path] !== sha ||
        JSON.stringify([...module_dependencies[module]].sort()) !==
          JSON.stringify([...deps[module]].sort())
      )
        throw Error(`Shared module differs between submissions: ${module}`);
    }
  }
  return {
    source_files,
    module_dependencies,
    build_order,
    package_imports: [...package_imports].sort(),
  };
}

function main() {
  const head = process.env.GITHUB_SHA,
    repository = process.env.GITHUB_REPOSITORY;
  if (
    !/^[a-f0-9]{40}$/.test(head ?? "") ||
    !/^[\w.-]+\/[\w.-]+$/.test(repository ?? "")
  )
    throw Error("Invalid build identity");
  const root = resolve(fileURLToPath(new URL("../..", import.meta.url)));
  const out = join(root, "verification");
  mkdirSync(out, { recursive: true });
  // Extract main's submissions once from immutable Git objects.
  const tree = mkdtempSync(join(out, "cache-source-"));
  execFileSync(
    "sh",
    [
      "-c",
      'git -C "$1" archive "$2" submissions | tar -x -C "$3"',
      "sh",
    ].concat([root, head, tree]),
  );
  const directories = readdirSync(join(tree, "submissions")).sort();
  const loaded = new Map();
  const load = (id) => {
    if (!loaded.has(id))
      loaded.set(
        id,
        submissionFiles(
          join(tree, "submissions", submissionDirectory(id, directories)),
        ),
      );
    return loaded.get(id);
  };
  const imports = new Map();
  const importsOf = (file) => {
    if (!imports.has(file.sha256))
      imports.set(file.sha256, leanImports(file.bytes.toString()));
    return imports.get(file.sha256);
  };
  const prepared = [];
  for (const directory of directories) {
    const id = submissionId(directory);
    try {
      const graph = dependencyGraph(id, load);
      const source_files = {},
        package_imports = [];
      for (const { file } of graph.modules.values()) {
        source_files[file.path] = file.sha256;
        package_imports.push(
          ...importsOf(file).filter((name) =>
            /^(PrimeNumberTheoremAnd|RellichKondrachov)(\.|$)/.test(name),
          ),
        );
      }
      prepared.push({
        id,
        files: new Map(
          [...graph.modules.values()].map(({ file }) => [file.path, file]),
        ),
        contract: {
          build_order: graph.order,
          module_dependencies: graph.dependencies,
          source_files,
          package_imports,
        },
      });
    } catch (error) {
      console.log(`Skipping ${id}: ${error.message}`);
    }
  }
  const merged = mergeContracts(prepared);
  const target = join(out, "prepared");
  for (const path of Object.keys(merged.source_files)) {
    const { files } = prepared.find((p) => p.files.has(path));
    const file = join(target, "submission", path);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, files.get(path).bytes, { mode: 0o444 });
  }
  rmSync(tree, { recursive: true, force: true });
  writeFileSync(
    join(target, "contract.json"),
    JSON.stringify(
      {
        schema_version: 2,
        purpose: "shared-build-cache",
        repository,
        head_sha: head,
        source_commit: head,
        ...merged,
        library_inventory_sha256: null,
      },
      null,
      2,
    ) + "\n",
  );
  writeFileSync(
    join(out, "imports.json"),
    JSON.stringify(merged.package_imports) + "\n",
  );
  console.log(
    `Prepared ${merged.build_order.length} shared modules from ${prepared.length} submissions at ${head}`,
  );
}

if (
  process.argv[1] &&
  resolve(process.argv[1]) === fileURLToPath(import.meta.url)
)
  main();
