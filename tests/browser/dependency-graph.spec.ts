import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";
import { cmp } from "../../core/rational.mjs";
import { verifiedHere } from "../../core/catalogue.mjs";

test("submissions open as a dependency graph that links back to details", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/?tab=submissions");

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
  await graph
    .getByRole("button", { name: new RegExp(`^${child.title}, θ`) })
    .click();
  await expect(page.locator(".graph-detail .proof-detail")).toContainText(
    child.method,
  );

  await graph
    .getByRole("group", { name: "Submission view" })
    .getByRole("button", { name: "List" })
    .click();
  await expect(page).toHaveURL(/mode=list/);
  await expect(graph).toHaveCount(0);
  await expect(page.locator(".leaderboard")).toBeVisible();
});

test("graph settings are kept in the URL and survive a reload", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/?tab=submissions");
  const graph = page.getByRole("region", { name: "Dependency graph" });
  await graph.getByRole("button", { name: "Generations" }).click();
  await graph.getByRole("button", { name: "Direct" }).click();
  await expect(page).toHaveURL(/axis=generations/);
  await expect(page).toHaveURL(/edges=direct/);

  await page.reload();
  await expect(
    graph.getByRole("button", { name: "Generations" }),
  ).toHaveAttribute("aria-pressed", "true");
  await expect(graph.getByRole("button", { name: "Direct" })).toHaveAttribute(
    "aria-pressed",
    "true",
  );
});

test("the front page shows the ancestry of the best submission", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/");
  const ancestry = page.getByRole("region", {
    name: "Ancestry graph of best submission",
  });
  const best = data.records
    .filter(verifiedHere)
    .sort((a, b) => cmp(a.theta, b.theta))[0];
  const expected = new Set<string>();
  const walk = (id: string) => {
    const r = data.records.find((r) => r.id === id);
    if (!r || expected.has(id)) return;
    expected.add(id);
    r.builds_on.forEach(walk);
  };
  walk(best.id);
  await expect(ancestry.locator("circle.node")).toHaveCount(expected.size);
  const ids = await ancestry
    .locator("circle.node")
    .evaluateAll((nodes) => nodes.map((n) => n.getAttribute("data-node")!));
  expect(ids.sort()).toEqual([...expected].sort());

  await page
    .getByRole("region", { name: "Contributor leaderboard" })
    .getByRole("link", { name: "See all" })
    .click();
  await expect(page).toHaveURL(/tab=contributors/);
});
