import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";

test("front page ranks contributors; submissions are bound sorted and best-bound links expand details", async ({
  page,
}) => {
  const source = catalogue().records[0];
  const records = [
    ["base", "1", "1", "Baseline"],
    ["a", "3", "4", "Alice"],
    ["b", "7", "10", "Bob"],
    ["c", "3", "5", "Alice"],
  ].map(([id, numerator, denominator, name], i) => ({
    ...source,
    id,
    title: id,
    theta: { numerator, denominator },
    authors: [{ name }],
    exact_bound: undefined,
    bound_interval: undefined,
    timeline_at: `2026-01-0${i + 1}T00:00:00Z`,
  }));
  await routeCatalogue(page, { schema_version: 1, records: records.reverse() });
  await page.goto("/");
  const board = page.getByRole("region", { name: "Contributor leaderboard" });
  await expect(board.locator("tbody tr")).toHaveCount(3);
  await expect(board.locator("tbody tr").first()).toContainText("Alice");
  await expect(board.locator("tbody tr").first()).toContainText("3.5e-1");
  await expect(board.locator("tbody tr").first().getByRole("link")).toHaveText(
    "0.6",
  );
  await board.getByRole("button", { name: /Alice/ }).click();
  await expect(board.locator(".contributor-submission")).toHaveCount(2);
  await expect(board.locator(".contributor-submission").first()).toContainText(
    "a",
  );
  await board
    .locator(".contributor-submission")
    .last()
    .getByRole("link", { name: "c", exact: true })
    .click();
  await expect(page).toHaveURL(/tab=submissions/);
  const table = page.getByRole("region", { name: "Submissions" });
  await expect(table.locator("tbody tr[id]").first()).toHaveAttribute(
    "id",
    "entry-c",
  );
  await expect(page.locator("#toggle-c")).toHaveAttribute(
    "aria-expanded",
    "true",
  );
  await page.getByRole("link", { name: /Timeline/ }).click();
  await expect(board).toBeVisible();
  await page.getByRole("link", { name: /Submissions/ }).click();
  await expect(table.locator("thead")).toContainText("Bound θ");
  await expect(
    page
      .getByRole("navigation", { name: "Research views" })
      .getByRole("link", { name: /Leaderboard/ }),
  ).toHaveCount(0);
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= innerWidth,
    ),
  ).toBe(true);
});
