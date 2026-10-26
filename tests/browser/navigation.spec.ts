import { test, expect, type Page } from "@playwright/test";
import { routeCatalogue } from "./catalogue-fixture";

const nav = (page: Page) =>
  page.getByRole("navigation", { name: "Research views" });
const curve = (page: Page) => page.locator(".verified-frontier");
const tabLink = (page: Page, name: string) =>
  nav(page).getByRole("link", { name, exact: name !== "Leaderboard" });

async function graphSnapshot(page: Page) {
  await expect(curve(page)).toHaveAttribute("d", /^M/);
  return page.locator(".chart").evaluate((svg) => ({
    curve: svg.querySelector(".verified-frontier")!.getAttribute("d"),
    axes: Array.from(svg.querySelectorAll("[data-axis]")).map(
      (el) => el.textContent,
    ),
    points: Array.from(svg.querySelectorAll("[data-dot] circle[stroke]")).map(
      (el) => [
        el.getAttribute("cx"),
        el.getAttribute("cy"),
        el.getAttribute("r"),
      ],
    ),
  }));
}

test("tab links survive refresh, direct visits and back/forward", async ({
  page,
  context,
}) => {
  await routeCatalogue(page);
  await page.goto("/?preview=keep#main");
  for (const name of ["Leaderboard", "Milestones", "Protocol", "Timeline"]) {
    await tabLink(page, name).click();
    expect(new URL(page.url()).searchParams.get("tab")).toBe(
      name.toLowerCase(),
    );
    expect(new URL(page.url()).searchParams.get("preview")).toBe("keep");
    expect(new URL(page.url()).hash).toBe("#main");
    await page.reload();
    await expect(tabLink(page, name)).toHaveAttribute("aria-current", "page");
  }
  await page.goBack();
  await expect(tabLink(page, "Protocol")).toHaveAttribute(
    "aria-current",
    "page",
  );
  await page.goBack();
  await expect(
    page.getByRole("heading", { name: "From one to the critical line" }),
  ).toBeVisible();
  await page.goForward();
  await expect(tabLink(page, "Protocol")).toHaveAttribute(
    "aria-current",
    "page",
  );

  const href = await tabLink(page, "Milestones").getAttribute("href");
  const shared = await context.newPage();
  await routeCatalogue(shared);
  await shared.goto(href!);
  await expect(tabLink(shared, "Milestones")).toHaveAttribute(
    "aria-current",
    "page",
  );
  await shared.close();
});

test("graph mode, zoom and pan survive reload, sharing and tab changes", async ({
  page,
  context,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  const fitted = await graphSnapshot(page);
  expect(new URL(page.url()).searchParams.get("view")).toBe("leaderboard");
  await page.getByRole("button", { name: "Zoom in", exact: true }).click();
  const chart = page.locator(".chart");
  await chart.focus();
  await chart.press("ArrowRight");
  await chart.press("ArrowDown");
  const zoomed = await graphSnapshot(page);
  const url = page.url();
  expect(new URL(url).searchParams.has("x")).toBe(true);
  expect(new URL(url).searchParams.has("y")).toBe(true);
  expect(zoomed).not.toEqual(fitted);
  await page.reload();
  await expect.poll(() => graphSnapshot(page)).toEqual(zoomed);
  await tabLink(page, "Milestones").click();
  await tabLink(page, "Timeline").click();
  await expect.poll(() => graphSnapshot(page)).toEqual(zoomed);

  const shared = await context.newPage();
  await routeCatalogue(shared);
  await shared.goto(url);
  await expect.poll(() => graphSnapshot(shared)).toEqual(zoomed);
  await shared.close();

  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  const full = await graphSnapshot(page);
  expect(new URL(page.url()).searchParams.get("view")).toBe("overview");
  expect(new URL(page.url()).searchParams.has("x")).toBe(false);
  expect(new URL(page.url()).searchParams.has("y")).toBe(false);
  await page.goBack();
  await expect.poll(() => graphSnapshot(page)).toEqual(zoomed);
  await page.goForward();
  await expect.poll(() => graphSnapshot(page)).toEqual(full);
  await page.getByRole("button", { name: "Zoom out", exact: true }).click();
  await chart.focus();
  await chart.press("Home");
  await expect.poll(() => graphSnapshot(page)).toEqual(fitted);
});

test("continuous wheel and drag gestures each take one history step", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const initial = await graphSnapshot(page);
  const historyLength = await page.evaluate(() => history.length);
  const chart = page.locator(".chart");
  await chart.evaluate((svg) => {
    const bounds = svg.getBoundingClientRect();
    for (let i = 0; i < 4; i++)
      svg.dispatchEvent(
        new WheelEvent("wheel", {
          bubbles: true,
          cancelable: true,
          deltaX: 12,
          deltaY: -20,
          clientX: bounds.x + bounds.width / 2,
          clientY: bounds.y + bounds.height / 2,
        }),
      );
  });
  const wheeled = await graphSnapshot(page);
  expect(wheeled).not.toEqual(initial);
  expect(await page.evaluate(() => history.length)).toBe(historyLength + 1);
  await page.goBack();
  await expect.poll(() => graphSnapshot(page)).toEqual(initial);
  await page.goForward();
  await expect.poll(() => graphSnapshot(page)).toEqual(wheeled);

  await chart.scrollIntoViewIfNeeded();
  const box = (await chart.boundingBox())!;
  await page.mouse.move(box.x + box.width * 0.7, box.y + box.height * 0.7);
  await page.mouse.down();
  await page.mouse.move(box.x + box.width * 0.8, box.y + box.height * 0.8, {
    steps: 5,
  });
  await page.mouse.up();
  const dragged = await graphSnapshot(page);
  expect(dragged).not.toEqual(wheeled);
  expect(await page.evaluate(() => history.length)).toBe(historyLength + 2);
  await page.reload();
  await expect.poll(() => graphSnapshot(page)).toEqual(dragged);
  await page.goBack();
  await expect.poll(() => graphSnapshot(page)).toEqual(wheeled);
});

test("invalid URL values fall back to a finite default viewport", async ({
  page,
}) => {
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await routeCatalogue(page);
  await page.goto("/");
  const initial = await graphSnapshot(page);
  for (const query of [
    "tab=missing&view=missing&x=NaN,Infinity&y=-1,NaN",
    "x=100,0&y=0,1",
    "x=0,1e300&y=1e300,0",
    "x=1,1&y=,",
  ]) {
    await page.goto(`/?${query}`);
    await expect(tabLink(page, "Timeline")).toHaveAttribute(
      "aria-current",
      "page",
    );
    await expect.poll(() => graphSnapshot(page)).toEqual(initial);
  }
  expect(errors).toEqual([]);
});
