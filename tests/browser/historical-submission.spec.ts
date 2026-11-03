import { test, expect } from "@playwright/test";
import { routeCatalogue, record } from "./catalogue-fixture";

test("historical imports keep their original date and an additional verification-independent tag", async ({
  page,
}) => {
  const imported = record({
    id: "historical-import",
    title: "Historical import fixture",
    historical: true,
    timeline_at: "2030-10-01T00:00:00Z",
    date_label: "Historical source created",
    submitted_at: "2030-10-08T09:00:00Z",
    first_verified_at: "2030-10-10T12:00:00Z",
    pr: 123,
  });
  await routeCatalogue(page, { schema_version: 1, records: [imported] });
  await page.goto("/");
  await page.getByRole("link", { name: /Submissions/ }).click();
  const entry = page.locator("#entry-historical-import");
  await expect(entry.locator(".historical-submission-tag")).toHaveText(
    "Historical",
  );
  await expect(entry.locator(".verification-badge")).toHaveAttribute(
    "title",
    "Verified in our framework",
  );
  await expect(entry.locator("time")).toHaveAttribute(
    "datetime",
    "2030-10-01T00:00:00Z",
  );
  await page.getByRole("button", { name: imported.title, exact: true }).click();
  const details = entry.locator(".proof-detail");
  await expect(details).toContainText("Historical source created");
  await expect(details).toContainText("01 Oct 2030");
  await expect(details).toContainText("2030-10-08 09:00:00 UTC");
  await expect(details).toContainText("2030-10-10 12:00:00 UTC");
  for (const width of [320, 390]) {
    await page.setViewportSize({ width, height: 844 });
    await expect(
      entry.locator(".entry-heading .historical-submission-tag"),
    ).toBeVisible();
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= innerWidth,
      ),
    ).toBe(true);
  }
});
