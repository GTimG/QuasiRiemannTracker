import { test, expect, type Page } from "@playwright/test";
import { readFileSync } from "node:fs";

async function expectReadableLabels(page: Page) {
  const problems = await page.locator(".chart").evaluate((svg) => {
    // Clip-path definitions have no screen rectangle; compare SVG coordinates.
    const bounds = (el: SVGGraphicsElement) => {
      const b = el.getBBox();
      return {
        left: b.x,
        right: b.x + b.width,
        top: b.y,
        bottom: b.y + b.height,
      };
    };
    const clip = bounds(svg.querySelector<SVGRectElement>("clipPath rect")!);
    const boxes = [...svg.querySelectorAll<SVGTextElement>(".point-label")]
      .filter((el) => getComputedStyle(el).visibility !== "hidden")
      .map((el) => ({ name: el.textContent, box: bounds(el) }));
    const errors: string[] = [];
    boxes.forEach(({ name, box }, i) => {
      if (
        box.left < clip.left ||
        box.right > clip.right ||
        box.top < clip.top ||
        box.bottom > clip.bottom
      )
        errors.push(`${name} clipped`);
      for (const other of boxes.slice(i + 1)) {
        if (
          box.left < other.box.right &&
          box.right > other.box.left &&
          box.top < other.box.bottom &&
          box.bottom > other.box.top
        )
          errors.push(`${name} overlaps ${other.name}`);
      }
    });
    return errors;
  });
  expect(problems).toEqual([]);
}

test("nearby chart names stay readable through resizing, filtering and zoom", async ({
  page,
  isMobile,
}) => {
  await page.goto("/");
  await expect(page.locator("[data-dot]")).toHaveCount(6);
  if (!isMobile) {
    const newest = page.locator(
      '[data-id="akashlevy-20261009-weighted-numerator"] .point-label',
    );
    const previous = page.locator(
      '[data-id="nielstron-20261009-tightening"] .point-label',
    );
    await expect(newest).toBeVisible();
    await expect(previous).toBeVisible();
    await expectReadableLabels(page);
    await page.screenshot({ path: ".work/labels-desktop.png", fullPage: true });
    await page
      .locator(".chart-panel")
      .screenshot({ path: ".work/labels-chart.png" });
    for (const width of [1080, 850, 700]) {
      await page.setViewportSize({ width, height: 1000 });
      await expect
        .poll(() =>
          page
            .locator(".chart")
            .evaluate((el) =>
              Math.abs(
                (el as SVGSVGElement).viewBox.baseVal.width -
                  el.parentElement!.getBoundingClientRect().width,
              ),
            ),
        )
        .toBeLessThan(1);
      const plotWidth = await page
        .locator(".chart")
        .evaluate((el) => (el as SVGSVGElement).viewBox.baseVal.width);
      if (plotWidth > 600) await expect(newest).toBeVisible();
      else await expect(newest).toHaveCount(0);
      await expectReadableLabels(page);
    }
    await page.getByLabel("Contribution type").selectOption("verified");
    await expect(page.locator("[data-dot]")).toHaveCount(4);
    await expectReadableLabels(page);
    await page.getByRole("button", { name: "Zoom out", exact: true }).click();
    await expectReadableLabels(page);
    await page.getByRole("button", { name: "Fit chart", exact: true }).click();
    await expectReadableLabels(page);
  } else {
    await expectReadableLabels(page);
    await page.screenshot({ path: ".work/labels-mobile.png", fullPage: true });
  }
  await page
    .locator('[data-id="nielstron-20261009-tightening"]')
    .press("Enter");
  await expect(page.locator(".proof-detail")).toContainText("Nielstron");
});

test("a crowded cluster retains its newest name and every selectable dot", async ({
  page,
  isMobile,
}) => {
  test.skip(
    isMobile,
    "Narrow screens use the accessible dots and table without persistent labels.",
  );
  // Crowd the chart only in an intercepted test response; never publish fixtures.
  const data = JSON.parse(readFileSync("catalogue/results.json", "utf8"));
  const source = data.records.find(
    (r: { id: string }) => r.id === "nielstron-20261009-tightening",
  );
  const cluster = Array.from({ length: 8 }, (_, i) => ({
    ...source,
    id: `label-fixture-${i}`,
    title:
      i === 7 ? "Newest crowded contribution" : `Crowded contribution ${i}`,
    timeline_at: new Date(Date.UTC(2026, 9, 10) + i).toISOString(),
    builds_on: [],
  }));
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({
      json: {
        ...data,
        records: [...data.records, ...cluster],
      },
    }),
  );
  await page.goto("/");
  await expect(page.locator('[data-id^="label-fixture-"]')).toHaveCount(8);
  await expect(
    page.locator('[data-id="label-fixture-7"] .point-label'),
  ).toBeVisible();
  expect(
    await page
      .locator('[data-id^="label-fixture-"] .point-label:visible')
      .count(),
  ).toBeLessThan(8);
  await expectReadableLabels(page);
  await page.locator('[data-id="label-fixture-0"]').press("Enter");
  await expect(page.locator(".proof-detail")).toContainText(
    "Crowded contribution 0",
  );
});
