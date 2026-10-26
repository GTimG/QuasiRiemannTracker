import { test, expect } from "@playwright/test";
import { cmp, decimal } from "../../core/rational.mjs";
import {
  catalogue as fixtureCatalogue,
  routeCatalogue,
} from "./catalogue-fixture";

const catalogue = fixtureCatalogue();
const verified = catalogue.records.filter(
  (record: { status: string }) => record.status === "framework-verified",
);
const best = [...verified].sort((a, b) => cmp(a.theta, b.theta))[0];

test("the default view focuses verified improvements and reset restores it", async ({
  page,
}) => {
  const source = verified[0];
  const historical = {
    ...source,
    id: "historical-1922-fixture",
    title: "Historical boundary from 1922",
    status: "historical-baseline",
    theta: { numerator: "1", denominator: "1" },
    timeline_at: "1922-01-01T00:00:00Z",
    date_precision: "year",
    date_label: "Publication year",
    first_verified_at: "",
    receipt_url: "",
    log_url: "",
    entrypoint: { module: "", declaration: "" },
    builds_on: [],
    references: [
      { label: "Publication", url: "https://example.com/historical" },
    ],
  };
  const weaker = {
    ...source,
    id: "verified-weaker-fixture",
    title: "Later verified weaker bound",
    theta: { numerator: "29", denominator: "33" },
    timeline_at: "2034-01-01T00:00:00Z",
    first_verified_at: "2034-01-01T00:00:00Z",
    builds_on: [],
  };
  const pending = {
    ...source,
    id: "pending-better-fixture",
    title: "Pending stronger claim",
    status: "verification-pending",
    theta: { numerator: "1", denominator: "2" },
    timeline_at: "1859-01-01T00:00:00Z",
    first_verified_at: "",
    builds_on: [],
  };
  await routeCatalogue(page, {
    ...catalogue,
    records: [...catalogue.records, historical, weaker, pending],
  });
  await page.goto("/");

  const chart = page.locator(".chart");
  const fit = page.getByRole("button", {
    name: "Fit leaderboard",
    exact: true,
  });
  const summary = page.getByRole("button", {
    name: "View best verified proof",
  });
  const boundTicks = chart.locator('[data-axis="bound"]');
  const dateTicks = chart.locator('[data-axis="date"]');
  await expect(chart.locator("[data-dot]").first()).toBeAttached();

  await expect(
    page.getByRole("group", { name: "Chart view", exact: true }),
  ).toHaveCount(0);
  await expect(chart.locator(`[data-id="${best.id}"]`)).toBeVisible();
  await expect(
    chart.locator('[data-id="historical-1922-fixture"]'),
  ).toHaveAttribute("aria-hidden", "true");
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toHaveAttribute("aria-hidden", "true");
  await expect(chart.locator('[data-id="pending-better-fixture"]')).toHaveCount(
    0,
  );
  const initialBounds = await boundTicks.allTextContents();
  expect(initialBounds).toHaveLength(5);
  for (const text of initialBounds) {
    const theta = Number(text.replace("…", ""));
    expect(theta).toBeGreaterThan(0.874);
    expect(theta).toBeLessThan(0.876);
  }
  const initialDates = await dateTicks.allTextContents();
  expect(initialDates.every((date) => date.includes("Oct"))).toBe(true);
  const summaryText = await summary.innerText();
  expect(summaryText).toContain(decimal(best.theta, 8).replace("…", ""));
  for (const result of [historical, weaker, pending]) {
    await expect(
      page.getByRole("button", { name: result.title, exact: true }),
    ).toBeVisible();
  }

  const pointCount = await chart.locator("[data-dot]").count();
  await chart.focus();
  for (let i = 0; i < 30; i++) await chart.press("-");
  await expect(chart.locator("[data-dot]")).toHaveCount(pointCount);
  await expect(
    chart.locator('[data-id="historical-1922-fixture"]'),
  ).toHaveAttribute("aria-hidden", "false");
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toHaveAttribute("aria-hidden", "false");
  await expect(chart.locator('[data-id="pending-better-fixture"]')).toHaveCount(
    0,
  );
  const years = (await dateTicks.allTextContents()).map(Number);
  expect(Math.min(...years)).toBeLessThan(1922);
  expect(Math.max(...years)).toBeGreaterThan(2034);
  expect(await summary.innerText()).toBe(summaryText);

  await chart.press("ArrowRight");
  await chart.press("ArrowUp");
  await fit.click();
  await expect(boundTicks).toHaveText(initialBounds);
  await expect(dateTicks).toHaveText(initialDates);
  await expect(chart.locator("[data-dot]")).toHaveCount(pointCount);
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toHaveAttribute("aria-hidden", "true");
  expect(await summary.innerText()).toBe(summaryText);

  await chart.focus();
  await chart.press("+");
  await chart.press("ArrowLeft");
  await chart.press("ArrowDown");
  await chart.press("Home");
  await expect(boundTicks).toHaveText(initialBounds);
  await expect(dateTicks).toHaveText(initialDates);
});

test("a verified theta-one baseline connects to the next bound while leaderboard zoom stays below one", async ({
  page,
}) => {
  const initial = verified[0];
  const classical = {
    ...initial,
    id: "verified-classical-fixture",
    title: "Verified classical baseline",
    theta: { numerator: "1", denominator: "1" },
    timeline_at: "1922-01-01T00:00:00Z",
    date_precision: "year",
    date_label: "Historical year",
    first_verified_at: "2026-10-12T17:39:36Z",
    builds_on: [],
  };
  await routeCatalogue(page, {
    ...catalogue,
    records: [
      classical,
      ...catalogue.records.filter(
        (r: { id: string }) => r.status !== "historical-baseline",
      ),
    ],
  });
  await page.goto("/");
  const chart = page.locator(".chart");
  const point = chart.locator('[data-id="verified-classical-fixture"]');
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(point).toHaveAttribute("aria-hidden", "true");
  for (const text of await chart
    .locator('[data-axis="bound"]')
    .allTextContents())
    expect(Number(text.replace("…", ""))).toBeLessThan(1);
  await chart.focus();
  for (let i = 0; i < 30; i++) await chart.press("-");
  await expect(point).toHaveAttribute("aria-hidden", "false");
  const coordinates = async (id: string) => {
    const circle = chart.locator(`[data-id="${id}"] circle`).first();
    return [await circle.getAttribute("cx"), await circle.getAttribute("cy")];
  };
  const [x1, y1] = await coordinates(classical.id),
    [x2, y2] = await coordinates(initial.id);
  expect(await chart.locator(".verified-frontier").getAttribute("d")).toMatch(
    new RegExp(`^M ${x1} ${y1} H ${x2} V ${y2}`.replaceAll(".", "\\.")),
  );
});
