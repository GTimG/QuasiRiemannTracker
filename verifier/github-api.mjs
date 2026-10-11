// Dependency-free API reads for trusted orchestration.
export async function api(route, token = process.env.GITHUB_TOKEN) {
  const response = await fetch("https://api.github.com/" + route, {
    headers: {
      Accept: "application/vnd.github+json",
      "X-GitHub-Api-Version": "2022-11-28",
      Authorization: `Bearer ${token}`,
    },
  });
  if (!response.ok) throw Error(`GitHub API ${response.status} for ${route}`);
  return response.json();
}
export async function pages(route) {
  const result = [];
  for (let page = 1; page <= 100; page++) {
    const rows = await api(
      `${route}${route.includes("?") ? "&" : "?"}per_page=100&page=${page}`,
    );
    if (!Array.isArray(rows)) throw Error("Unexpected GitHub response");
    result.push(...rows);
    if (rows.length < 100) return result;
  }
  throw Error("GitHub pagination limit exceeded");
}
