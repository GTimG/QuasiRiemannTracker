import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";
import { cmp } from "../../core/rational.mjs";
test("submissions default to exact bound order and old leaderboard URLs still resolve", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/?tab=leaderboard&mode=list");
  const expected = [...data.records].sort((a, b) => cmp(a.theta, b.theta));
  const entries = page.locator(".contribution-list .leaderboard-entry");
  await expect(entries).toHaveCount(expected.length);
  await expect(entries.first()).toHaveAttribute(
    "id",
    `entry-${expected[0].id}`,
  );
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect(entries.first()).toHaveAttribute(
    "id",
    `entry-${expected.at(-1)!.id}`,
  );
  await expect(
    page.getByRole("region", { name: "Submissions", exact: true }),
  ).toBeVisible();
});
