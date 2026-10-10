import { test, expect } from "@playwright/test";
const repository = "GTimG/QuasiRiemannTracker";
const sample = {
  id: "test-proof",
  pr: 123,
  head_sha: "a".repeat(40),
  title: "Submitted proof fixture",
  authors: [{ name: "Test contributor" }],
  theta: { numerator: "3", denominator: "4" },
  submitted_at: "2026-10-10T12:00:00Z",
  state: "queued",
  run_url: `https://github.com/${repository}/actions/runs/42`,
};
test("pending submissions share table and details with verified results and appear on the graph", async ({
  page,
}) => {
  await page.route("**/submission-status/submissions.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        repository,
        records: [
          sample,
          { ...sample, pr: 124, state: "closed" },
          { ...sample, pr: 125, state: "superseded" },
        ],
      },
    }),
  );
  await page.goto("/");
  await expect(page.locator("tbody tr")).toHaveCount(6);
  await expect(page.locator("[data-dot]")).toHaveCount(6);
  const row = page.locator("tbody tr").filter({ hasText: sample.title });
  await expect(row).toContainText("Verification pending");
  await expect(row).toContainText("3/4");
  await expect(row).toContainText("Submitted");
  await expect(row).not.toContainText("Claimed");
  await expect(
    page.getByRole("heading", { name: "Pending submissions" }),
  ).toHaveCount(0);
  await row.getByRole("button").click();
  await expect(page.locator(".proof-detail")).toContainText("Checks queued");
  await expect(
    page.locator(".proof-detail").getByRole("link", { name: "Submission PR" }),
  ).toHaveAttribute("href", `https://github.com/${repository}/pull/123`);
  await expect(
    page.locator(".proof-detail").getByRole("link", { name: "Check logs" }),
  ).toHaveAttribute("href", sample.run_url);
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBe(true);
});
test("successful checks remain pending review and never get a verified badge", async ({
  page,
}) => {
  await page.route("**/submission-status/submissions.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        repository,
        records: [{ ...sample, state: "checks-passed" }],
      },
    }),
  );
  await page.goto("/");
  const row = page.locator("tbody tr").filter({ hasText: sample.title });
  await expect(row.locator(".tag.amber")).toHaveCount(1);
  await expect(row.locator(".tag.teal")).toHaveCount(0);
  await row.getByRole("button").click();
  await expect(page.locator(".proof-detail")).toContainText(
    "Checks passed · awaiting review",
  );
});
test("nonimproving pending bounds do not expand the initial plot", async ({
  page,
}) => {
  const better = {
    ...sample,
    theta: { numerator: "8749", denominator: "10000" },
  };
  const weaker = {
    ...sample,
    id: "weaker",
    pr: 124,
    title: "Weaker pending result",
    theta: { numerator: "29", denominator: "33" },
  };
  await page.route("**/submission-status/submissions.json", (route) =>
    route.fulfill({
      json: { schema_version: 1, repository, records: [better, weaker] },
    }),
  );
  await page.goto("/");
  await expect(page.locator("tbody tr")).toHaveCount(7);
  await expect(page.locator("[data-dot]")).toHaveCount(6);
  await expect(
    page.locator('[data-id="pending-123-test-proof"]'),
  ).toBeVisible();
  await expect(page.locator('[data-id="pending-124-weaker"]')).toHaveCount(0);
});
test("absence of the status branch leaves the existing website working", async ({
  page,
}) => {
  await page.route("**/submission-status/submissions.json", (route) =>
    route.fulfill({ status: 404, body: "Not found" }),
  );
  await page.goto("/");
  await expect(page.locator("tbody tr")).toHaveCount(5);
});
