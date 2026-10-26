import { test, expect } from "@playwright/test";
import { readFileSync } from "node:fs";
import { cmp, decimal } from "../../core/rational.mjs";
import { catalogue, routeCatalogue } from "./catalogue-fixture";
const fixtureRecords = catalogue().records;
const verifiedCount = fixtureRecords.filter(
  (record: { status: string }) => record.status === "framework-verified",
).length;
const pendingCount = fixtureRecords.filter(
  (record: { status: string }) => record.status === "verification-pending",
).length;
const recordsByBound = [...fixtureRecords].sort((a, b) =>
  cmp(a.theta, b.theta),
);
const bestVerified = recordsByBound.find(
  (record) => record.status === "framework-verified",
);
const plottedCount = fixtureRecords.filter((record: { status: string }) =>
  ["framework-verified", "historical-baseline"].includes(record.status),
).length;
const chartFixtures = () =>
  JSON.parse(
    readFileSync(
      new URL("../fixtures/chart-records.json", import.meta.url),
      "utf8",
    ),
  );
test.beforeEach(async ({ page }) => {
  await routeCatalogue(page);
});

test("verified results expose the source and verification links supplied by the catalogue", async ({
  page,
}) => {
  await page.goto("/");
  for (const record of fixtureRecords.filter(
    (record) => record.status === "framework-verified",
  )) {
    await page.getByRole("button", { name: record.title, exact: true }).click();
    await expect(
      page.getByRole("link", { name: "Verification record", exact: true }),
    ).toHaveAttribute("href", "/" + record.certificate_url);
    await expect(
      page.getByRole("link", { name: "Checked Lean solution", exact: true }),
    ).toHaveAttribute("href", record.solution_url!);
  }
});

test("mixed verification statuses and exact bounds render from the supplied catalogue", async ({
  page,
}, info) => {
  await page.goto("/");
  await expect(page.locator(".leaderboard-entry")).toHaveCount(
    fixtureRecords.length,
  );
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(page.locator("[data-dot]")).toHaveCount(plottedCount);
  await expect(page.locator(".leaderboard .tag.teal")).toHaveCount(
    verifiedCount,
  );
  await expect(page.locator(".leaderboard .tag.amber")).toHaveCount(
    pendingCount,
  );
  const algebraic = fixtureRecords.find(
    (record) => record.id === "fixture-algebraic",
  )!;
  await page
    .getByRole("button", { name: algebraic.title, exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "(1507 − 2√921) / 1653",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "Verification pending",
  );
  await expect(
    page.getByRole("link", { name: "Verification record", exact: true }),
  ).toHaveCount(0);
  await page
    .getByRole("button", { name: bestVerified.title, exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("87489/100000");
  await expect(page.locator(".proof-detail")).toContainText("Example team");
  await expect(page.locator(".proof-detail")).toContainText(
    "Verified in our framework",
  );
  await page.getByRole("button", { name: "Close proof details" }).click();
  await page.evaluate(() => window.scrollTo(0, 0));
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-catalogue-fixture.png`,
    fullPage: true,
  });
});
test("selection, exact sorting and zoom", async ({ page }, info) => {
  await page.goto("/");
  await page
    .getByRole("button", {
      name: "Example author · Initial bound",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("7/8");
  await page.getByRole("button", { name: "Close proof details" }).click();
  const plot = page.getByRole("group", { name: /Interactive bound timeline/ });
  await plot.focus();
  await page.keyboard.press("+");
  await page.keyboard.press("ArrowRight");
  await page.keyboard.press("Home");
  await page.getByRole("button", { name: "Zoom in", exact: true }).click();
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(
    page.locator(".leaderboard-entry").first().locator(".entry-decimal"),
  ).toHaveText(decimal(bestVerified.theta, 14));
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect(
    page
      .locator(".leaderboard-entry")
      .first()
      .getByRole("button", {
        name: recordsByBound.at(-1).title,
        exact: true,
      }),
  ).toBeVisible();
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect(
    page.locator(".leaderboard-entry").first().getByRole("button", {
      name: recordsByBound[0].title,
      exact: true,
    }),
  ).toBeVisible();
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-interactions.png`,
    fullPage: true,
  });
});
test("dialog keyboard controls, protocol, responsive overflow and no errors", async ({
  page,
}) => {
  const errors: string[] = [];
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto("/");
  await page
    .getByRole("button", { name: "Submit a proof", exact: true })
    .click();
  await expect(page.getByRole("dialog")).toBeVisible();
  await page.keyboard.press("Escape");
  await expect(page.getByRole("dialog")).not.toBeVisible();
  await page.getByRole("link", { name: "Protocol", exact: true }).click();
  await expect(
    page.getByRole("heading", { name: "Requirements" }),
  ).toBeVisible();
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBeTruthy();
  expect(errors).toEqual([]);
});

test("sub-float bounds remain visibly separate after narrowing time, with safe wheel zoom", async ({
  page,
  isMobile,
}, info) => {
  // Synthetic values exist only in this isolated browser test response.
  const fixtures = chartFixtures();
  await page.clock.setFixedTime(
    Math.max(
      ...fixtures.records.map((r: { first_verified_at: string }) =>
        Date.parse(r.first_verified_at),
      ),
    ),
  );
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({ json: { schema_version: 1, records: fixtures.records } }),
  );
  await page.goto("/");
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  const plot = page.getByRole("group", { name: /Interactive bound timeline/ });
  await plot.focus();
  for (let i = 0; i < 3; i++) await page.keyboard.press("ArrowRight");
  // Shift zooms only time, preserving the automatic exact vertical range.
  for (let i = 0; i < 4; i++) await page.keyboard.press("Shift+Equal");
  const first = page.getByRole("button", {
    name: "Select A sub-float improvement, theta 87499974999999999999/100000000000000000000",
    exact: true,
  });
  const second = page.getByRole("button", {
    name: "Select Another sub-float improvement, theta 43749987499999999999/50000000000000000000",
    exact: true,
  });
  await expect(first).toBeVisible();
  await expect(second).toBeVisible();
  const y1 = Number(await first.locator("circle").last().getAttribute("cy"));
  const y2 = Number(await second.locator("circle").last().getAttribute("cy"));
  expect(Math.abs(y1 - y2)).toBeGreaterThan(100);
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-tiny-improvements.png`,
    fullPage: true,
  });
  if (!isMobile) {
    const warnings: string[] = [];
    page.on("console", (m) => {
      if (m.type() === "error") warnings.push(m.text());
    });
    const plot = page.getByRole("group", {
      name: /Interactive bound timeline/,
    });
    await plot.hover();
    const before = await plot.locator("path").first().getAttribute("d");
    await page.mouse.wheel(0, -100);
    await expect
      .poll(() => plot.locator("path").first().getAttribute("d"))
      .not.toBe(before);
    expect(warnings.filter((x) => x.includes("passive"))).toEqual([]);
  }
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBeTruthy();
});

test("a stronger pending submission stays in the table and cannot move the verified curve", async ({
  page,
}) => {
  await page.goto("/");
  await expect(
    page.locator(`[data-dot][data-id="${bestVerified.id}"]`),
  ).toBeVisible();
  const pointCount = await page.locator("[data-dot]").count();
  const before = await page.locator(".verified-frontier").getAttribute("d");
  // The chart can appear before MathJax replaces the raw TeX with rendered math.
  const bestBound = page.locator(".best-bound mjx-container");
  await expect(bestBound).toBeVisible();
  const best = await bestBound.textContent();
  const pending = {
    ...fixtureRecords.find((r: { id: string }) => r.id === "fixture-newest"),
    id: "pending-test-only",
    title: "Pending test contribution",
    status: "verification-pending",
    first_verified_at: "",
    builds_on: [],
    theta: { numerator: "1", denominator: "2" },
    timeline_at: "2030-10-11T00:00:00Z",
    date_label: "Submitted",
  };
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        records: [...fixtureRecords, pending],
      },
    }),
  );
  await page.reload();
  await expect(page.locator(".leaderboard-entry")).toHaveCount(
    fixtureRecords.length + 1,
  );
  await expect(page.locator("[data-dot]")).toHaveCount(pointCount);
  await expect(page.locator('[data-id="pending-test-only"]')).toHaveCount(0);
  await expect(bestBound).toHaveText(best!);
  await expect(page.locator(".verified-frontier")).toHaveAttribute(
    "d",
    before!,
  );
  await page
    .getByRole("button", { name: "Pending test contribution", exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "Verification pending",
  );
});
