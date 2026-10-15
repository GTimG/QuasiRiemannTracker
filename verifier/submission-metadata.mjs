import { submissionDependencies } from "./submission-dependencies.mjs";
// Publication metadata lives beside the Lean source in metadata.json.
const text = (value, limit) =>
  typeof value === "string" && value.trim().length > 0 && value.length <= limit;
const url = (value) => {
  try {
    const parsed = new URL(value);
    return parsed.protocol === "https:" && !parsed.username && !parsed.password;
  } catch {
    return false;
  }
};
export function validateSubmissionMetadata(value) {
  const fields = new Set([
    "title",
    "authors",
    "description",
    "license",
    "builds_on",
    "references",
    "dependencies",
  ]);
  if (
    !value ||
    typeof value !== "object" ||
    Array.isArray(value) ||
    Object.keys(value).some((key) => !fields.has(key)) ||
    !text(value.title, 240) ||
    !text(value.description, 10000) ||
    !Array.isArray(value.authors) ||
    !value.authors.length ||
    value.authors.length > 100 ||
    value.authors.some(
      (author) =>
        !author ||
        typeof author !== "object" ||
        Array.isArray(author) ||
        Object.keys(author).some((key) => !["name", "url"].includes(key)) ||
        !text(author.name, 240) ||
        (author.url !== undefined && !url(author.url)),
    ) ||
    (value.license !== undefined && !text(value.license, 1000)) ||
    (value.builds_on !== undefined &&
      (!Array.isArray(value.builds_on) ||
        value.builds_on.length > 100 ||
        new Set(value.builds_on).size !== value.builds_on.length ||
        value.builds_on.some((id) => !/^[a-z][a-z0-9-]{2,63}$/.test(id)))) ||
    (value.references !== undefined &&
      (!Array.isArray(value.references) ||
        value.references.length > 100 ||
        value.references.some(
          (reference) =>
            !reference ||
            typeof reference !== "object" ||
            Array.isArray(reference) ||
            Object.keys(reference).some(
              (key) => !["label", "url"].includes(key),
            ) ||
            !text(reference.label, 240) ||
            !url(reference.url),
        )))
  )
    throw Error(
      "Invalid publication metadata: provide title, authors and description in metadata.json",
    );
  submissionDependencies(value);
  return value;
}

export function parseSubmissionMetadata(body) {
  const blocks = [
    ...(body ?? "").matchAll(
      /^```qrh-metadata[ \t]*\r?\n([\s\S]*?)^```[ \t]*$/gm,
    ),
  ];
  if (blocks.length !== 1)
    throw Error(
      "New bounds require exactly one fenced qrh-metadata JSON block in the PR body",
    );
  let value;
  try {
    value = JSON.parse(blocks[0][1]);
  } catch {
    throw Error("The qrh-metadata block must contain valid JSON");
  }
  return validateSubmissionMetadata(value);
}

// Fetch data from the immutable PR head; never follow a branch or execute source.
export async function readSubmissionSources(
  request,
  { repository, head_sha, result_id },
) {
  if (
    !/^[\w.-]+\/[\w.-]+$/.test(repository ?? "") ||
    !/^[a-f0-9]{40}$/.test(head_sha ?? "") ||
    !/^[a-z][a-z0-9-]{2,63}$/.test(result_id ?? "")
  )
    throw Error("Invalid submission metadata identity");
  const tree = async (sha) => {
    const value = await request(`repos/${repository}/git/trees/${sha}`);
    if (value.truncated || !Array.isArray(value.tree))
      throw Error("Incomplete submission tree");
    return value.tree;
  };
  const entry = (entries, name, type) => {
    const matches = entries.filter((file) => file.path === name);
    const value = matches[0];
    if (
      matches.length !== 1 ||
      value.type !== type ||
      !(type === "tree" ? ["040000"] : ["100644", "100755"]).includes(
        value.mode,
      ) ||
      !/^[a-f0-9]{40}$/.test(value.sha)
    )
      throw Error(`Expected a regular submission ${name}`);
    return value;
  };
  const root = await tree(head_sha);
  const entries = await tree(entry(root, "submissions", "tree").sha);
  const trees = {},
    done = new Set(),
    active = new Set();
  let metadata;
  async function visit(id) {
    if (active.has(id)) throw Error(`Cyclic submission dependencies: ${id}`);
    if (done.has(id)) return;
    if (Object.keys(trees).length >= 256)
      throw Error("Submission dependency limit");
    active.add(id);
    const revision = entry(entries, id, "tree");
    trees[id] = revision.sha;
    const contents = await tree(revision.sha);
    const blob = entry(contents, "metadata.json", "blob");
    const source = await tree(entry(contents, "src", "tree").sha);
    const candidate = await tree(entry(source, "Candidate", "tree").sha);
    entry(candidate, "Main.lean", "blob");
    const file = await request(`repos/${repository}/git/blobs/${blob.sha}`);
    if (
      file.encoding !== "base64" ||
      typeof file.content !== "string" ||
      file.size > 65536
    )
      throw Error("Expected a regular submission metadata.json");
    const bytes = Buffer.from(file.content, "base64");
    if (bytes.length > 65536) throw Error("Submission metadata is too large");
    const value = JSON.parse(bytes.toString("utf8"));
    if (id === result_id) metadata = validateSubmissionMetadata(value);
    for (const dep of submissionDependencies(value)) await visit(dep);
    active.delete(id);
    done.add(id);
  }
  await visit(result_id);
  return { metadata, trees };
}
export async function readSubmissionMetadata(request, expected) {
  return (await readSubmissionSources(request, expected)).metadata;
}
