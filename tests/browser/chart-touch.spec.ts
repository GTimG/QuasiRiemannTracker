import { test, expect } from "@playwright/test";
import { routeCatalogue } from "./catalogue-fixture";

test("single touch preserves graph; two fingers pan and pinch", async ({
  page,
  isMobile,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const plot = page.locator("svg.chart");
  const curve = plot.locator(".verified-frontier");
  await expect(curve).toHaveAttribute("d", /^M/);
  const initial = (await curve.getAttribute("d"))!;
  const touch = async (type: string, points: number[][]) =>
    plot.evaluate(
      (el, { type, points }) => {
        const touches = points.map(
          ([clientX, clientY], identifier) =>
            new Touch({ identifier, target: el, clientX, clientY }),
        );
        return el.dispatchEvent(
          new TouchEvent(type, { bubbles: true, cancelable: true, touches }),
        );
      },
      { type, points },
    );
  expect(await touch("touchstart", [[150, 200]])).toBe(true);
  expect(await touch("touchmove", [[150, 240]])).toBe(true);
  await expect(curve).toHaveAttribute("d", initial);
  await expect(
    page.getByText("Use two fingers to move the graph", { exact: true }),
  ).toBeVisible();
  expect(
    await touch("touchstart", [
      [120, 200],
      [220, 200],
    ]),
  ).toBe(false);
  await expect(page.locator(".chart-touch-hint")).toHaveCount(0);
  expect(
    await touch("touchmove", [
      [100, 210],
      [250, 210],
    ]),
  ).toBe(false);
  await expect(curve).not.toHaveAttribute("d", initial);
  await touch("touchend", []);
  const after = (await curve.getAttribute("d"))!;
  await touch("touchstart", [[150, 200]]);
  await touch("touchmove", [[150, 250]]);
  await expect(curve).toHaveAttribute("d", after);
  await expect(plot).toHaveCSS("touch-action", "pan-y");
  await expect(
    page.getByRole("button", { name: "Zoom in", exact: true }),
  ).toHaveCSS("width", isMobile ? "30px" : "27px");
});
