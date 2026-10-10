import { test, expect } from "@playwright/test";
import { readFileSync } from "node:fs";
const liveRecords = JSON.parse(
  readFileSync(new URL("../../catalogue/results.json", import.meta.url), "utf8"),
).records;
const verifiedCount = liveRecords.filter(
  (record: { status: string }) => record.status === "framework-verified",
).length;
const pendingCount = liveRecords.length - verifiedCount;
const chartFixtures = () =>
  JSON.parse(
    readFileSync(
      new URL("../fixtures/chart-records.json", import.meta.url),
      "utf8",
    ),
  );
test("status panels follow an admitted registry (isolated mock response)", async ({
  page,
  request,
}) => {
  const fixtures = chartFixtures();
  await page.route("**/registry.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        records: [{ ...fixtures.records[0], id: "openai-baseline" }],
        events: [],
        active_ids: ["openai-baseline"],
        baseline_status: "verified",
      },
    }),
  );
  await page.goto("/");
  await page.getByRole("button", { name: "Protocol", exact: true }).click();
  await expect(
    page.getByText("Signed registry entries link to Comparator", {
      exact: false,
    }),
  ).toBeVisible();
  await expect(
    page.getByText(
      "The separate Comparator and NanoDa checking service is not yet running.",
      { exact: false },
    ),
  ).toHaveCount(0);
});
test("five real results, verification statuses and source downloads", async ({
  page,
  request,
}, info) => {
  await page.goto("/");
  await expect(page.locator("tbody tr")).toHaveCount(5);
  await expect(page.locator("[data-dot]")).toHaveCount(5);
  await expect(page.locator("tbody .tag.teal")).toHaveCount(verifiedCount);
  await expect(page.locator("tbody .tag.amber")).toHaveCount(pendingCount);
  await page
    .getByRole("button", {
      name: "Baiying Liu · optimized parameters",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "(1507 − 2√921) / 1653",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    liveRecords.find((record: { id: string }) => record.id === "liu-20261008")
      .status === "framework-verified"
      ? "Verified in our framework"
      : "Verification pending",
  );
  await expect(page.locator(".proof-detail")).not.toContainText(
    "Signed verification receipt",
  );
  await page
    .getByRole("button", {
      name: "ProofCouncil · certified uniform descent",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "874957019421/1000000000000",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "Tim Gehrunger · ProofCouncil",
  );
  const proof = await request.get("/proofs/qrh-20261009/Nonvanishing.lean");
  expect(proof.ok()).toBeTruthy();
  expect(await proof.text()).toContain(
    "theorem DirichletCharacter.LFunction_ne_zero_of_theta_lt_re",
  );
  await expect(page.getByRole("button", { name: "Nielstron · compressed rational refinement", exact: true })).toHaveCount(0);
  const native = await request.get("/proofs/nielstron-20261009-tightening/native-lean-verification.json");
  expect(native.ok()).toBeTruthy();
  const nativeReport = await native.json();
  expect(nativeReport.status).toBe("PASS");
  expect(nativeReport.external_checker_status).toContain("Not checked");
  const independent = await request.get("/proofs/nielstron-20261009-kernels/result.json");
  expect(independent.ok()).toBeTruthy();
  const independentReport = await independent.json();
  expect(independentReport.status).toBe("PASS");
  expect(independentReport.kernels).toEqual(["Lean default", "nanoda", "con-ron"]);
  expect(independentReport.source_commit).toBe("49331e02e2c04bb2388ae9c6e9ea424c23b96ac6");
  await page
    .getByRole("button", { name: "Nielstron · exact algebraic endpoint", exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("Verified in our framework");
  await expect(page.locator(".proof-detail")).toContainText("874957019420098946128603850561452983/1000000000000000000000000000000000000");
  await expect(page.locator(".proof-detail")).toContainText("657e³−954e²+21e+20=0");
  await expect(page.locator(".proof-detail")).not.toContainText("Signed verification receipt");
  const algebraic = await request.get("/proofs/nielstron-algebraic-20261009-kernels/result.json");
  expect(algebraic.ok()).toBeTruthy();
  const algebraicReport = await algebraic.json();
  expect(algebraicReport.status).toBe("PASS");
  expect(algebraicReport.declarations).toHaveLength(7);
  expect(algebraicReport.declarations).toContain("QRHPalomar.existsUniqueRoot");
  expect(algebraicReport.kernels).toEqual(["Lean default", "nanoda", "con-ron"]);
  expect(algebraicReport.source_commit).toBe("2fc2b0b7f2b9510df4618936e1b2ccd58f7d9171");
  expect(algebraicReport.signed_admission).toBe(false);
  const catalogue = await (await request.get("/catalogue.json")).json();
  const current = catalogue.records.filter((r: { id: string }) => r.id.startsWith("nielstron-"));
  expect(current).toHaveLength(1);
  expect(current[0].id).toBe("nielstron-20261009-tightening");
  expect(current[0].proof_revision).toBe("nielstron-algebraic-20261009");
  expect(catalogue.historical_records).toHaveLength(1);
  await expect(page.getByRole("link", { name: "Previous N24 independent kernel report (historical revision)" })).toBeVisible();
  const reg = await (await request.get("/registry.json")).json();
  expect(reg.records).toEqual([]);
  await page.getByRole("button", { name: "Close proof details" }).click();
  await page.evaluate(() => window.scrollTo(0, 0));
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-live.png`,
    fullPage: true,
  });
});
test("selection, exact sorting, filters and zoom", async ({ page }, info) => {
  await page.goto("/");
  await page
    .getByRole("button", { name: "OpenAI · seven eighths", exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("7/8");
  await expect(page.locator(".proof-detail")).toContainText("con-ron");
  await page.getByRole("button", { name: "Close proof details" }).click();
  const plot = page.getByRole("group", { name: /Interactive bound timeline/ });
  await plot.focus();
  await page.keyboard.press("+");
  await page.keyboard.press("ArrowRight");
  await page.keyboard.press("Home");
  await page.getByRole("button", { name: "Zoom in", exact: true }).click();
  await page.getByRole("button", { name: "Fit chart", exact: true }).click();
  await page.getByLabel("Sort contributions").selectOption("bound");
  await expect(page.locator("tbody tr").first()).toContainText("exact algebraic endpoint");
  await page.getByLabel("Contribution type").selectOption("verified");
  await expect(page.locator("tbody tr")).toHaveCount(verifiedCount);
  await page.getByLabel("Contribution type").selectOption("pending");
  await expect(page.locator("tbody tr")).toHaveCount(pendingCount);
  await page.getByLabel("Contribution type").selectOption("all");
  await page.getByLabel("Search contributions").fill("Tim Gehrunger");
  await expect(page.locator("tbody tr")).toHaveCount(1);
  await page.getByLabel("Search contributions").fill("");
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
  await page.getByRole("button", { name: "Protocol", exact: true }).click();
  await expect(
    page.getByRole("heading", { name: "Required proof checks" }),
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
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({ json: { schema_version: 1, records: [] } }),
  );
  const fixtures = chartFixtures();
  await page.route("**/registry.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        records: fixtures.records,
        events: [],
        active_ids: fixtures.records.map((r: { id: string }) => r.id),
        baseline_status: "verified",
      },
    }),
  );
  await page.goto("/");
  await page.getByLabel("Timeline start").fill("70");
  await page.getByLabel("Timeline end").fill("90");
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
    await page.keyboard.down("Control");
    await page.mouse.wheel(0, -100);
    await page.keyboard.up("Control");
    await expect(page.getByLabel("Timeline start")).not.toHaveValue("70");
    expect(warnings.filter((x) => x.includes("passive"))).toEqual([]);
  }
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBeTruthy();
});
