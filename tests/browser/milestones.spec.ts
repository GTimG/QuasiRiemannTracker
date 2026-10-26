import { test, expect } from "@playwright/test";
import { routeCatalogue, record } from "./catalogue-fixture";

test("milestone overview is opt-in and both fit controls preserve points", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const chart = page.locator(".chart");
  await expect(chart.locator("[data-dot]").first()).toBeAttached();
  const initialBounds = await chart
    .locator('[data-axis="bound"]')
    .allTextContents();
  const initialDates = await chart
    .locator('[data-axis="date"]')
    .allTextContents();
  const count = await chart.locator("[data-dot]").count();
  for (const text of initialBounds) {
    expect(Number(text.replace("…", ""))).toBeGreaterThan(0.874);
    expect(Number(text.replace("…", ""))).toBeLessThan(0.876);
  }
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  for (const id of ["one", "thirteen-fifteenths", "three-quarters", "half"]) {
    const line = chart.locator(`[data-milestone="${id}"]`);
    const y = Number(await line.getAttribute("y1"));
    expect(y).toBeGreaterThan(35);
    expect(y).toBeLessThan(295);
    expect(await line.getAttribute("y2")).toBe(String(y));
    expect(await line.getAttribute("stroke-dasharray")).toBe(
      ["one", "half"].includes(id) ? null : "7 5",
    );
  }
  const bounds = await chart.locator('[data-axis="bound"]').allTextContents();
  expect(Number(bounds[0].replace("…", ""))).toBeGreaterThan(1);
  expect(Number(bounds.at(-1)!.replace("…", ""))).toBeLessThan(0.5);
  await expect(chart.locator("[data-dot]")).toHaveCount(count);
  await chart.focus();
  await chart.press("+");
  await chart.press("ArrowDown");
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(bounds);
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(initialBounds);
  for (const text of await chart
    .locator('[data-axis="bound"]')
    .allTextContents()) {
    expect(Number(text.replace("…", ""))).toBeGreaterThan(0.874);
    expect(Number(text.replace("…", ""))).toBeLessThan(0.876);
  }
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  await chart.focus();
  await chart.press("Home");
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(initialBounds);
  await expect(chart.locator('[data-axis="date"]')).toHaveText(initialDates);
});

test("milestones sit between leaderboard and protocol and fit narrow screens", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const nav = page.getByRole("navigation", { name: "Research views" });
  await expect(nav.getByRole("link")).toHaveText([
    "Timeline",
    /Leaderboard/,
    "Milestones",
    "Protocol",
  ]);
  await nav.getByRole("link", { name: "Milestones", exact: true }).click();
  await expect(
    page.getByRole("heading", { name: "From one to the critical line" }),
  ).toBeVisible();
  await expect(page.locator(".milestone-list > li")).toHaveCount(4);
  await expect(page.locator(".milestone-source")).toHaveCount(4);
  await expect(page.locator(".milestone-list h3")).toHaveText([
    "Classical result",
    "Limit of OpenAI’s method",
    "The three-quarter barrier",
    "Generalized Riemann Hypothesis",
  ]);
  await expect(page.locator(".milestone-list .eyebrow")).toHaveCount(0);
  for (const item of await page.locator(".milestone-list > li").all()) {
    const isAcerBarrier = await item
      .getByRole("heading", { name: "The three-quarter barrier" })
      .count();
    await expect(item.locator("p")).toHaveCount(isAcerBarrier ? 1 : 2);
    await expect(item.locator("mjx-container").first()).toBeVisible();
  }
  for (const width of [320, 390, 768]) {
    await page.setViewportSize({ width, height: 844 });
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= innerWidth,
      ),
    ).toBe(true);
    await expect(
      nav.getByRole("link", { name: "Protocol", exact: true }),
    ).toBeInViewport();
  }
});

test("overview dots are small and filled points paint above overlapping hollow points", async ({
  page,
}) => {
  const filled = record({ id: "a-frontier", title: "Frontier fixture" });
  const hollow = record({ id: "z-alternative", title: "Equal bound fixture" });
  await routeCatalogue(page, { schema_version: 1, records: [hollow, filled] });
  await page.goto("/?view=overview");
  const dots = page.locator("[data-dot]");
  await expect(dots).toHaveCount(2);
  const filledDot = page.locator('[data-dot][data-id="a-frontier"]');
  const hollowDot = page.locator('[data-dot][data-id="z-alternative"]');
  await expect(filledDot.locator("circle[stroke]")).toHaveAttribute("r", "2");
  await expect(hollowDot.locator("circle[stroke]")).toHaveAttribute("r", "2");
  await expect(hollowDot.locator("circle[stroke]")).toHaveAttribute(
    "fill",
    "white",
  );
  await expect(filledDot.locator("circle[stroke]")).toHaveAttribute(
    "fill",
    "#1d5d74",
  );
  const assertOrder = async () => {
    expect(
      await dots.evaluateAll((elements) =>
        elements.map((el) => el.getAttribute("data-id")),
      ),
    ).toEqual(["z-alternative", "a-frontier"]);
  };
  await assertOrder();
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await assertOrder();
  await page.getByRole("button", { name: hollow.title, exact: true }).click();
  await expect(hollowDot).toHaveAttribute("aria-pressed", "true");
  await assertOrder();
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(filledDot.locator("circle[stroke]")).toHaveAttribute("r", "5");
  await assertOrder();
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  await expect(filledDot.locator("circle[stroke]")).toHaveAttribute("r", "2");
});
