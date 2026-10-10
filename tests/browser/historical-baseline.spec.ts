import { test, expect } from "@playwright/test";

test("historical theta = 1 stays distinct from verification and recent results remain accessible", async ({
  page,
}) => {
  await page.goto("/");
  const baseline = page.locator(
    '[data-dot][data-id="classical-euler-product"]',
  );
  await expect(baseline).toBeVisible();
  await expect(page.locator(".chart")).toContainText("1922");
  await baseline.press("Enter");
  const detail = page.locator(".proof-detail");
  await expect(detail).toContainText("Historical baseline");
  await expect(detail).toContainText("1922 (year only)");
  await expect(detail).not.toContainText("1922-01-01");
  await expect(detail).not.toContainText("Verified in our framework");
  await expect(detail).not.toContainText("Pending");
  await expect(detail.locator(".exact-result strong")).toHaveText("1/1");
  await page.getByRole("button", { name: "Close proof details" }).click();

  await page.getByLabel("Contribution type").selectOption("pending");
  await expect(
    page.getByRole("button", {
      name: "Classical baseline · θ = 1",
      exact: true,
    }),
  ).toHaveCount(0);
  await page.getByLabel("Contribution type").selectOption("historical");
  await expect(page.locator("tbody tr")).toHaveCount(1);
  await expect(page.locator("tbody .tag.historical")).toHaveText(
    "Historical baseline",
  );
  await page.getByLabel("Contribution type").selectOption("all");

  await page
    .getByRole("button", { name: "Recent results", exact: true })
    .click();
  await expect(baseline).toHaveCount(0);
  await expect(page.locator("[data-dot]")).toHaveCount(5);
  const xs = await page
    .locator("[data-dot] circle:first-of-type")
    .evaluateAll((dots) => dots.map((dot) => Number(dot.getAttribute("cx"))));
  expect(Math.max(...xs) - Math.min(...xs)).toBeGreaterThan(100);
  await page.getByRole("button", { name: "Full history", exact: true }).click();
  await expect(baseline).toBeVisible();
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBeTruthy();
});
