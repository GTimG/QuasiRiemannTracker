import { test, expect } from "@playwright/test";

const baseline = {
  id: "test-historical-baseline",
  title: "Classical baseline · θ = 1",
  authors: [{ name: "Classical Euler-product theorem" }],
  theta: { numerator: "1", denominator: "1" },
  status: "historical-baseline",
  timeline_at: "1922-01-01T00:00:00Z",
  date_precision: "year",
  date_label: "Early QRH-era formulation",
  first_verified_at: "",
  entrypoint: { module: "", declaration: "" },
  method: "Absolute convergence of the Euler product.",
  verification_note: "Classical theorem included as historical context.",
  license: "Historical references linked",
  builds_on: [],
  references: [
    { label: "Theorem reference", url: "https://example.com/theorem" },
  ],
};

test("historical catalogue entries display their status and year precision", async ({
  page,
}) => {
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({
      json: { schema_version: 1, records: [baseline] },
    }),
  );
  await page.goto("/");
  const row = page.locator(".leaderboard-entry");
  await expect(row.locator(".tag.historical")).toHaveText(
    "Historical baseline",
  );
  const date = row.locator(".entry-meta time");
  await expect(date).toHaveText("1922");
  await expect(date).toHaveAttribute("datetime", "1922");
  await expect(date).toHaveAttribute(
    "title",
    `${baseline.date_label}: ${baseline.timeline_at}`,
  );
  await page.getByRole("button", { name: baseline.title, exact: true }).click();
  const detail = page.locator(".proof-detail");
  await expect(detail).toContainText("Historical baseline");
  await expect(detail).toContainText("1922 (year only)");
  await expect(detail.locator(".exact-result strong")).toHaveText("1/1");
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBe(true);
});
