import { pages } from "./github-api.mjs";

const managed = [
  {
    name: "new-bound",
    color: "0e8a16",
    description: "Contains proof, submission, or catalogue changes",
    kind: "proof",
  },
  {
    name: "maintenance",
    color: "5319e7",
    description: "Contains website, documentation, or infrastructure changes",
    kind: "maintenance",
  },
];

export async function syncPRLabels(repository, number, classification) {
  if (
    typeof repository !== "string" ||
    repository !== repository.trim() ||
    !/^[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+$/.test(repository) ||
    [".", ".."].includes(repository.split("/")[1]) ||
    !Number.isSafeInteger(number) ||
    number < 1
  )
    throw Error("Invalid repository or PR number for managed labels");
  if (
    !classification ||
    typeof classification !== "object" ||
    Array.isArray(classification) ||
    Object.keys(classification).sort().join(",") !== "maintenance,proof" ||
    typeof classification.proof !== "boolean" ||
    typeof classification.maintenance !== "boolean"
  )
    throw Error("Invalid PR change classification for managed labels");
  const token = process.env.GITHUB_TOKEN;
  if (typeof token !== "string" || !token.trim())
    throw Error("GITHUB_TOKEN is required to synchronize PR labels");
  const request = (route, method = "GET", body) =>
    fetch(`https://api.github.com/${route}`, {
      method,
      headers: {
        Accept: "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        Authorization: `Bearer ${token}`,
        ...(body ? { "Content-Type": "application/json" } : {}),
      },
      ...(body ? { body: JSON.stringify(body) } : {}),
    });
  const requireSuccess = (response, route) => {
    if (!response.ok) throw Error(`GitHub API ${response.status} for ${route}`);
  };
  const confirmLabel = async (response, route, name) => {
    requireSuccess(response, route);
    const label = await response.json();
    if (typeof label?.name !== "string" || label.name.toLowerCase() !== name)
      throw Error(`Unexpected GitHub label response for ${route}`);
  };
  const ensureLabel = async (label) => {
    const route = `repos/${repository}/labels/${encodeURIComponent(label.name)}`;
    let response = await request(route);
    if (response.status === 404) {
      const createRoute = `repos/${repository}/labels`;
      response = await request(createRoute, "POST", {
        name: label.name,
        color: label.color,
        description: label.description,
      });
      // Another PR run can create the same repository label concurrently.
      // Confirm that the label exists after a concurrent creation attempt.
      if (response.status === 422) response = await request(route);
      else requireSuccess(response, createRoute);
    }
    await confirmLabel(response, route, label.name);
  };

  const issueRoute = `repos/${repository}/issues/${number}/labels`;
  const current = await pages(issueRoute);
  if (
    current.some(
      (label) => typeof label?.name !== "string" || !label.name.length,
    )
  )
    throw Error("Unexpected GitHub PR labels response");
  const desired = managed.filter((label) => classification[label.kind]);
  for (const label of desired) await ensureLabel(label);
  const names = new Set(current.map((label) => label.name.toLowerCase()));
  const missing = desired
    .map((label) => label.name)
    .filter((name) => !names.has(name));
  if (missing.length)
    requireSuccess(
      await request(issueRoute, "POST", { labels: missing }),
      issueRoute,
    );
  const wanted = new Set(desired.map((label) => label.name));
  const owned = new Set(managed.map((label) => label.name));
  for (const label of current) {
    const name = label.name.toLowerCase();
    if (!owned.has(name) || wanted.has(name)) continue;
    const route = `${issueRoute}/${encodeURIComponent(label.name)}`;
    const response = await request(route, "DELETE");
    if (response.status !== 404) requireSuccess(response, route);
  }
  return desired.map((label) => label.name);
}
