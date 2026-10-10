import { test, expect } from "@playwright/test";

test("diagonal trackpad gestures preserve both pan and zoom", async ({
  page,
  isMobile,
}) => {
  test.skip(isMobile, "Desktop trackpad interaction");
  await page.goto("/");
  const plot = page.getByRole("group", { name: /Interactive bound timeline/ });
  const curve = plot.locator(".verified-frontier");
  await expect(curve).toHaveAttribute("d", /^M/);
  const initial = (await curve.getAttribute("d"))!;
  const reset = async () => {
    await page.getByRole("button", { name: "Fit chart", exact: true }).click();
    await expect(curve).toHaveAttribute("d", initial);
  };
  const wheel = async (deltaX: number, deltaY: number) => {
    const before = await curve.getAttribute("d");
    await plot.evaluate(
      (svg, delta) => {
        const bounds = svg.getBoundingClientRect();
        svg.dispatchEvent(
          new WheelEvent("wheel", {
            bubbles: true,
            cancelable: true,
            clientX: bounds.x + bounds.width / 2,
            clientY: bounds.y + bounds.height / 2,
            deltaX: delta.x,
            deltaY: delta.y,
          }),
        );
      },
      { x: deltaX, y: deltaY },
    );
    await expect(curve).not.toHaveAttribute("d", before!);
    return (await curve.getAttribute("d"))!;
  };

  const zoomOnly = await wheel(0, -60);
  await reset();
  const panOnly = await wheel(80, 0);
  await reset();
  const diagonal = await wheel(80, -60);
  expect(diagonal).not.toBe(zoomOnly);
  expect(diagonal).not.toBe(panOnly);
  await reset();
  await wheel(80, 0);
  const sequential = await wheel(0, -60);
  expect(diagonal).toBe(sequential);
});
