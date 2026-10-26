import { test, expect, type Page } from "@playwright/test";
import { catalogue, record, routeCatalogue } from "./catalogue-fixture";

const viewedAt = Date.parse("2030-10-12T12:00:00Z");

async function expectFrontierEndsAt(page: Page, at: number) {
  const geometry = await page.locator(".chart").evaluate((svg) => {
    const point = (id: string) => {
      const dot = svg.querySelector(`[data-id="${id}"]`)!;
      return {
        at: Number(dot.getAttribute("data-time")),
        x: Number(dot.querySelector("circle")!.getAttribute("cx")),
      };
    };
    const path = svg.querySelector(".verified-frontier") as SVGPathElement;
    const last = path.getPointAtLength(path.getTotalLength());
    return {
      first: point("fixture-baseline"),
      next: point("fixture-improvement"),
      lastX: last.x,
      right: (svg as SVGSVGElement).viewBox.baseVal.width - 24,
    };
  });
  const expectedX =
    geometry.first.x +
    ((at - geometry.first.at) / (geometry.next.at - geometry.first.at)) *
      (geometry.next.x - geometry.first.x);
  expect(geometry.lastX).toBeCloseTo(expectedX, 2);
  return geometry;
}

test("the frontier stops at the viewing time, including after pan, zoom and a later visit", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const chart = page.locator(".chart");
  await expect(chart.locator(".verified-frontier")).toHaveAttribute("d", /^M/);
  const initial = await expectFrontierEndsAt(page, viewedAt);
  expect(initial.lastX).toBeLessThan(initial.right - 1);

  await chart.focus();
  await chart.press("-");
  await chart.press("ArrowRight");
  await expectFrontierEndsAt(page, viewedAt);
  await chart.press("Home");

  // Weeks without a new record still extend the history to the new visit,
  // while preserving the narrow vertical range of the verified bounds.
  const later = Date.parse("2030-11-12T12:00:00Z");
  await page.clock.setFixedTime(later);
  await page.reload();
  await expect(chart.locator(".verified-frontier")).toHaveAttribute("d", /^M/);
  const revisited = await expectFrontierEndsAt(page, later);
  expect(revisited.lastX).toBeLessThan(revisited.right - 1);
  expect(revisited.lastX).toBeGreaterThan(revisited.next.x);
  for (const label of await chart
    .locator('[data-axis="bound"]')
    .allTextContents()) {
    expect(Number(label.replace("…", ""))).toBeGreaterThan(0.874);
    expect(Number(label.replace("…", ""))).toBeLessThan(0.876);
  }
});

test("a future-dated contribution cannot extend the line beyond the viewing time", async ({
  page,
}) => {
  const data = catalogue();
  data.records.push(
    record({
      id: "future-fixture",
      theta: { numerator: "87488", denominator: "100000" },
      timeline_at: "2030-10-20T00:00:00Z",
      first_verified_at: "2030-10-20T12:00:00Z",
    }),
  );
  await routeCatalogue(page, data);
  await page.goto("/");
  await expect(page.locator(".verified-frontier")).toHaveAttribute("d", /^M/);
  await expectFrontierEndsAt(page, viewedAt);
});
