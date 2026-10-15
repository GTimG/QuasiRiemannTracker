import { leanImports } from "./actions/imports.mjs";

export const submissionPrefix = (id) =>
  `Submissions.${id.replaceAll("-", "_")}`;
export function submissionDependencies(metadata) {
  const ids = metadata.dependencies ?? [];
  if (
    !Array.isArray(ids) ||
    ids.length > 256 ||
    new Set(ids).size !== ids.length ||
    ids.some(
      (id) => typeof id !== "string" || !/^[a-z][a-z0-9-]{2,63}$/.test(id),
    )
  )
    throw Error("Invalid submission dependencies");
  return ids;
}

// The loader reads immutable source. Every dependency belongs to the same head.
export function dependencyGraph(id, load) {
  const submissions = new Map(),
    active = new Set();
  function visit(id) {
    if (active.has(id)) throw Error(`Cyclic submission dependencies: ${id}`);
    if (submissions.has(id)) return;
    if (submissions.size >= 256) throw Error("Submission dependency limit");
    active.add(id);
    const s = load(id);
    submissions.set(id, s);
    const metadata = JSON.parse(
      s.files.find((f) => f.path === "metadata.json").bytes.toString(),
    );
    s.dependencies = submissionDependencies(metadata);
    for (const dep of s.dependencies) visit(dep);
    active.delete(id);
  }
  visit(id);
  const modules = new Map();
  for (const [owner, s] of submissions) {
    const own = submissionPrefix(owner);
    for (const file of s.files.filter((f) => f.path.endsWith(".lean"))) {
      const name = file.path.slice(4, -5).replaceAll("/", ".");
      if (!name.startsWith("Candidate.") && !name.startsWith(own + "."))
        throw Error(`Module ${name} must belong to ${own}`);
      if (name.startsWith("Candidate.") && owner !== id) continue;
      if (modules.has(name))
        throw Error(`Duplicate submission module: ${name}`);
      modules.set(name, { owner, file });
    }
  }
  const order = [],
    dependencies = {},
    done = new Set(),
    visiting = new Set();
  function build(name) {
    if (done.has(name)) return;
    if (visiting.has(name)) throw Error(`Cyclic Lean imports: ${name}`);
    visiting.add(name);
    const { owner, file } = modules.get(name);
    const local = [];
    for (const dep of leanImports(file.bytes.toString())) {
      if (dep === "OAI" || dep.startsWith("OAI."))
        throw Error("Import OAI source through the openai-baseline submission");
      if (
        dep === "Candidate" ||
        dep.startsWith("Candidate.") ||
        dep === "Submissions" ||
        dep.startsWith("Submissions.")
      ) {
        const target = modules.get(dep);
        if (!target) throw Error(`Missing submission module: ${dep}`);
        if (
          owner !== target.owner &&
          !submissions.get(owner).dependencies.includes(target.owner)
        )
          throw Error(
            `Undeclared dependency: ${owner} imports ${target.owner}`,
          );
        local.push(dep);
        build(dep);
      }
    }
    visiting.delete(name);
    done.add(name);
    order.push(name);
    dependencies[name] = [...new Set(local)];
  }
  // Only the target import closure is compiled. Other submissions can provide
  // independent modules without importing every theorem they contain.
  build("Candidate.Main");
  return { submissions, modules, order, dependencies };
}

export function affectedSubmissions(changed, graph) {
  const affected = new Set(changed);
  let grew = true;
  while (grew) {
    grew = false;
    for (const [id, deps] of graph)
      if (!affected.has(id) && deps.some((dep) => affected.has(dep))) {
        affected.add(id);
        grew = true;
      }
  }
  return affected;
}
