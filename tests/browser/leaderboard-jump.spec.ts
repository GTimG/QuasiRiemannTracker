import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";

test("default ranking uses previous chronological submission and shows delta left, bound right", async ({
  page,
}) => {
  const source = catalogue().records[0];
  const records = [
    ["baseline", "1", "1"],
    ["big-jump", "3", "4"],
    ["small-jump", "7", "10"],
    ["equal", "7", "10"],
    ["regression", "4", "5"],
  ].map(([id, numerator, denominator], index) => ({
    ...source,
    id,
    title: id,
    exact_bound: undefined,
    bound_interval: undefined,
    theta: { numerator, denominator },
    timeline_at: `2026-01-0${index + 1}T00:00:00Z`,
  }));
  await routeCatalogue(page, { schema_version: 1, records: records.reverse() });
  await page.goto("/?tab=leaderboard");
  const entries = page.locator(".leaderboard-entry");
  const ids = () => entries.evaluateAll((es) => es.map((e) => e.id));
  await expect
    .poll(ids)
    .toEqual([
      "entry-big-jump",
      "entry-small-jump",
      "entry-equal",
      "entry-regression",
      "entry-baseline",
    ]);
  await expect(entries.nth(0).locator(".entry-delta")).toContainText("0.25");
  await expect(entries.nth(0).locator(".entry-bound-decimal")).toHaveText(
    "0.75",
  );
  await expect(entries.nth(0).locator(".entry-exact")).toHaveText("3/4");
  await expect(entries.nth(2).locator(".entry-delta")).toContainText("0");
  await expect(entries.nth(3).locator(".entry-delta")).toContainText("-0.1");
  await expect(entries.last().locator(".entry-delta")).toContainText("—");
  const deltaBox = await entries.first().locator(".entry-delta").boundingBox();
  const boundBox = await entries.first().locator(".entry-bound").boundingBox();
  expect(deltaBox!.x + deltaBox!.width).toBeLessThanOrEqual(boundBox!.x);
  await page
    .getByRole("button", { name: "Improvement Δθ", exact: true })
    .click();
  await expect
    .poll(ids)
    .toEqual([
      "entry-regression",
      "entry-equal",
      "entry-small-jump",
      "entry-big-jump",
      "entry-baseline",
    ]);
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect
    .poll(ids)
    .toEqual([
      "entry-equal",
      "entry-small-jump",
      "entry-big-jump",
      "entry-regression",
      "entry-baseline",
    ]);
  await page.screenshot({
    path: "test-results/leaderboard-jump.png",
    fullPage: true,
  });
});
