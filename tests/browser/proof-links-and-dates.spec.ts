import { test, expect } from "@playwright/test";
import {
  catalogue as fixtureCatalogue,
  routeCatalogue,
} from "./catalogue-fixture";

const catalogue = fixtureCatalogue();

test("verified proof badges open solution sources and contribution dates retain their meaning", async ({
  page,
}) => {
  await routeCatalogue(page, catalogue);
  await page.goto("/?tab=submissions");
  await expect(
    page.getByRole("button", { name: "Date", exact: true }),
  ).toBeVisible();
  for (const record of catalogue.records) {
    const row = page.locator(".contribution-list .leaderboard-entry").filter({
      has: page.getByRole("button", { name: record.title, exact: true }),
    });
    const badge = row.locator(".verification-badge");
    if (record.status === "framework-verified") {
      await expect(badge).toHaveAttribute("href", /\.lean$/);
      const href = (await badge.getAttribute("href"))!;
      expect(href).toBe(record.solution_url);
      expect(new URL(href).pathname).toMatch(/\/blob\/[a-f0-9]{40}\/.+\.lean$/);
    } else if (record.status === "historical-baseline") {
      await expect(row.locator(".tag.historical")).toHaveText(
        "Historical baseline",
      );
    } else {
      expect(record.status).toBe("verification-pending");
      await expect(badge).toHaveClass(/\bamber\b/);
      await expect(badge.locator("span")).toHaveText("Verification pending");
    }
    const dateCell = row;
    await expect(dateCell.locator("time")).toHaveAttribute(
      "datetime",
      record.date_precision === "year"
        ? record.timeline_at.slice(0, 4)
        : record.timeline_at,
    );
    await expect(dateCell.locator("time")).toHaveAttribute(
      "title",
      record.date_precision === "year"
        ? `${record.date_label}: ${record.timeline_at.slice(0, 4)} (year only)`
        : `${record.date_label}: ${record.timeline_at}`,
    );
  }
});
