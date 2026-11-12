import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";
import { decimal } from "../../core/rational.mjs";

test("entries expand in place, toggle with the keyboard, and restore focus on close", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/?mode=list");
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Submissions", exact: false })
    .click();
  const record = data.records[0];
  const toggle = page.getByRole("button", { name: record.title, exact: true });
  const entry = page.locator(`#entry-${record.id}`);
  await expect(entry.locator(".entry-decimal").first()).toContainText(
    decimal(record.theta, 14),
  );
  await expect(toggle).toHaveAttribute("aria-expanded", "false");
  await toggle.focus();
  await page.keyboard.press("Enter");
  await expect(toggle).toHaveAttribute("aria-expanded", "true");
  await expect(page.locator(".proof-detail")).toBeVisible();
  await expect(page.locator(".proof-detail")).toContainText(record.method);
  await expect(page.locator(".proof-detail")).toHaveCount(1);
  await page.keyboard.press("Space");
  await expect(page.locator(".proof-detail")).toHaveCount(0);
  await toggle.click();
  await page.getByRole("button", { name: "Close proof details" }).click();
  await expect(toggle).toBeFocused();
  await expect(toggle).toHaveAttribute("aria-expanded", "false");
  await toggle.click();
  const next = data.records.find((r) => r.id !== record.id)!;
  await page.getByRole("button", { name: next.title, exact: true }).click();
  await expect(page.locator(`#details-${record.id}`)).toHaveCount(0);
  await expect(page.locator(`#details-${next.id} .proof-detail`)).toBeVisible();
});

test("mobile submissions scroll within their table and preserve full details", async ({
  page,
  isMobile,
}) => {
  test.skip(!isMobile);
  const data = catalogue();
  const record = data.records.find((r) => r.id === "fixture-algebraic")!;
  record.authors = [
    { name: "An author with a particularly long display name" },
  ];
  record.method =
    "A submitted method description with enough detail to exceed one line on a narrow screen. The full explanation remains available in the expanded entry.";
  await routeCatalogue(page, data);
  await page.goto("/?mode=list");
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Submissions", exact: false })
    .click();
  const entry = page.locator(`#entry-${record.id}`);
  for (const width of [320, 390, 430]) {
    await page.setViewportSize({ width, height: 844 });
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= window.innerWidth,
      ),
    ).toBe(true);
  }
  await entry.getByRole("button", { name: record.title, exact: true }).click();
  await expect(page.locator(".proof-detail")).toContainText(
    record.authors[0].name,
  );
  await expect(page.locator(".proof-detail")).toContainText(record.method);
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBe(true);
});
