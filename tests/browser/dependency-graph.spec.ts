import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";

test("submissions switch to a dependency graph that links back to details", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/?tab=submissions");
  const views = page.getByRole("group", { name: "Submission view" });
  await views.getByRole("button", { name: "Graph" }).click();

  const graph = page.getByRole("region", { name: "Dependency graph" });
  await expect(graph.locator("circle.node")).toHaveCount(data.records.length);
  const edges = data.records.reduce(
    (n, r) =>
      n +
      r.builds_on.filter((id) => data.records.some((p) => p.id === id)).length,
    0,
  );
  await expect(graph.locator(".edges path")).toHaveCount(edges);

  const child = data.records.find((r) => r.builds_on.length)!;
  const node = graph.getByRole("button", {
    name: new RegExp(`^${child.title}, θ`),
  });
  await node.click();
  await expect(page.locator(".graph-detail .proof-detail")).toContainText(
    child.method,
  );

  await graph
    .getByRole("group", { name: "Submission view" })
    .getByRole("button", { name: "List" })
    .click();
  await expect(graph).toHaveCount(0);
  await expect(page.locator(".leaderboard")).toBeVisible();
});
