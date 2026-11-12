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
    timeline_at: `2026-01-0${i + 1}T00:00:00Z`,
  }));
  await routeCatalogue(page, { schema_version: 1, records: records.reverse() });
  await page.goto("/?mode=list");
  const board = page.getByRole("region", { name: "Contributor leaderboard" });
  await expect(board.locator(".contributor-summary")).toHaveCount(2);
  await expect(board.getByRole("heading")).toHaveCount(0);
  await expect(
    board.locator(".contributor-header mjx-container svg"),
  ).toBeVisible();
  await expect(
    page.getByRole("link", { name: /^Contributors\s*2$/ }),
  ).toBeVisible();
  await expect(board.locator(".contributor-summary").first()).toContainText(
    "Alice",
  );
  await expect(
    board.locator(".contributor-summary").first().locator("mjx-container svg"),
  ).toBeVisible();
  await expect(
    board.locator(".contributor-summary").first().locator("mjx-container"),
  ).toHaveAttribute("jax", "SVG");
  await expect(
    board
      .locator(".contributor-summary")
      .first()
      .locator('[data-mml-node="msup"]'),
  ).toHaveCount(1);
  await expect(board.locator(".contributor-summary").first()).not.toContainText(
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
  await expect(table.locator(".leaderboard-entry").first()).toHaveAttribute(
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
  await expect(
    table.getByRole("button", { name: "Exact bound θ" }),
  ).toBeVisible();
  await page.getByRole("link", { name: /^Contributors\s*2$/ }).click();
  await expect(board).toBeVisible();
  await expect(board).not.toContainText("Each coauthor");
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
