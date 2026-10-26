import { test, expect } from "@playwright/test";
import { catalogue, routeCatalogue } from "./catalogue-fixture";
import { decimal } from "../../core/rational.mjs";

test("entries expand in place, toggle with the keyboard, and restore focus on close", async ({
  page,
}) => {
  const data = catalogue();
  await routeCatalogue(page, data);
  await page.goto("/");
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Leaderboard", exact: false })
    .click();
  const record = data.records[0];
  const toggle = page.getByRole("button", { name: record.title, exact: true });
  const entry = page.locator(`#entry-${record.id}`);
  await expect(entry.locator(".entry-decimal")).toHaveText(
    decimal(record.theta, 14),
  );
  await expect(toggle).toHaveAttribute("aria-expanded", "false");
  await toggle.focus();
  await page.keyboard.press("Enter");
  await expect(toggle).toHaveAttribute("aria-expanded", "true");
  await expect(entry.locator(".proof-detail")).toBeVisible();
  await expect(entry.locator(".proof-detail")).toContainText(record.method);
  await expect(page.locator(".proof-detail")).toHaveCount(1);
  await page.keyboard.press("Space");
  await expect(entry.locator(".proof-detail")).toHaveCount(0);
  await toggle.click();
  await entry.getByRole("button", { name: "Close proof details" }).click();
  await expect(toggle).toBeFocused();
  await expect(toggle).toHaveAttribute("aria-expanded", "false");
  await toggle.click();
  const next = data.records.find((r) => r.id !== record.id)!;
  await page.getByRole("button", { name: next.title, exact: true }).click();
  await expect(entry.locator(".proof-detail")).toHaveCount(0);
  await expect(page.locator(`#entry-${next.id} .proof-detail`)).toBeVisible();
});

test("mobile metadata and method each occupy one row, with full text available on expansion", async ({
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
  await page.goto("/");
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Leaderboard", exact: false })
    .click();
  const entry = page.locator(`#entry-${record.id}`);
  for (const width of [320, 390, 430]) {
    await page.setViewportSize({ width, height: 844 });
    const boxes = await entry
      .locator(".entry-meta > *")
      .evaluateAll((elements) =>
        elements.map((e) => {
          const r = e.getBoundingClientRect();
          return { top: r.top, bottom: r.bottom };
        }),
      );
    expect(Math.max(...boxes.map((b) => b.top))).toBeLessThan(
      Math.min(...boxes.map((b) => b.bottom)),
    );
    const method = await entry.locator(".entry-method").evaluate((el) => ({
      height: el.clientHeight,
      lineHeight: parseFloat(getComputedStyle(el).lineHeight),
      width: el.clientWidth,
      scrollWidth: el.scrollWidth,
    }));
    expect(method.height).toBeLessThanOrEqual(Math.ceil(method.lineHeight));
    expect(method.scrollWidth).toBeGreaterThan(method.width);
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= window.innerWidth,
      ),
    ).toBe(true);
  }
  await entry.getByRole("button", { name: record.title, exact: true }).click();
  await expect(entry.locator(".proof-detail")).toContainText(
    record.authors[0].name,
  );
  await expect(entry.locator(".proof-detail")).toContainText(record.method);
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBe(true);
});
