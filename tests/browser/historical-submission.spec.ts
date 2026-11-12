import { test, expect } from "@playwright/test";
import { routeCatalogue, record } from "./catalogue-fixture";

test("public announcement dates and normal verification badges apply to imported results", async ({
  page,
}) => {
  const imported = record({
    id: "historical-import",
    title: "Historical import fixture",
    published_at: "2030-10-01T18:48:49Z",
    timeline_at: "2030-10-01T18:48:49Z",
    date_label: "Public announcement",
    submitted_at: "2030-10-08T09:00:00Z",
    first_verified_at: "2030-10-10T12:00:00Z",
    pr: 123,
  });
  await routeCatalogue(page, { schema_version: 1, records: [imported] });
  await page.goto("/?mode=list");
  await page.getByRole("link", { name: /Submissions/ }).click();
  const entry = page.locator("#entry-historical-import");
  await expect(entry.locator(".historical-submission-tag")).toHaveCount(0);
  await expect(entry.locator(".verification-badge")).toHaveAttribute(
    "title",
    "Verified in our framework",
  );
  await expect(entry.locator("time")).toHaveAttribute(
    "datetime",
    "2030-10-01T18:48:49Z",
  );
  await page.getByRole("button", { name: imported.title, exact: true }).click();
  const details = entry.locator(".proof-detail");
  await expect(details).toContainText("Public announcement");
  await expect(details).toContainText("2030-10-01 18:48:49 UTC");
  await expect(details).toContainText("2030-10-08 09:00:00 UTC");
  await expect(details).toContainText("2030-10-10 12:00:00 UTC");
  for (const width of [320, 390]) {
    await page.setViewportSize({ width, height: 844 });
    await expect(
      entry.locator(".entry-heading .historical-submission-tag"),
    ).toHaveCount(0);
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= innerWidth,
      ),
    ).toBe(true);
  }
});

test("day-only announcements do not display a fabricated midnight timestamp", async ({
  page,
}) => {
  const imported = record({
    id: "day-only-announcement",
    title: "Documented day-only announcement",
    timeline_at: "2030-10-01T00:00:00Z",
    published_at: "2030-10-01T00:00:00Z",
    date_precision: "day",
    date_label: "Public announcement",
  });
  await routeCatalogue(page, { schema_version: 1, records: [imported] });
  await page.goto("/?tab=submissions&mode=list");
  const entry = page.locator("#entry-day-only-announcement");
  await expect(entry.locator("time")).toHaveAttribute("datetime", "2030-10-01");
  await expect(entry.locator("time")).toHaveAttribute(
    "title",
    "Public announcement: 2030-10-01 (day only)",
  );
  await page.getByRole("button", { name: imported.title, exact: true }).click();
  const details = entry.locator(".proof-detail");
  await expect(details).toContainText("01 Oct 2030 (day only)");
  await expect(details).not.toContainText("2030-10-01 00:00:00 UTC");
});
