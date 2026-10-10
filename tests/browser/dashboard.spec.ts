import { test, expect } from "@playwright/test";
import { readFileSync } from "node:fs";
const liveRecords = JSON.parse(
  readFileSync(
    new URL("../../catalogue/results.json", import.meta.url),
    "utf8",
  ),
).records;
const verifiedCount = liveRecords.filter(
  (record: { status: string }) => record.status === "framework-verified",
).length;
const pendingCount = liveRecords.length - verifiedCount;
test("Cycle25 independent acceptance, lineage and historical paper evidence are accessible", async ({
  page,
  request,
}) => {
  await page.goto("/");
  await page
    .getByRole("button", {
      name: "Hailey Collet · quartic boundary",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "683505193/781250000",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "Verified in our framework",
  );
  await expect(page.locator(".proof-detail")).not.toContainText(
    "Signed verification receipt",
  );
  const link = page.getByRole("link", {
    name: "Historical contributor seven-target report",
    exact: true,
  });
  const report = await (
    await request.get((await link.getAttribute("href")) as string)
  ).json();
  expect(report.status).toBe("PASS");
  expect(report.theta_rational).toBe("683505193/781250000");
  expect(report.declarations).toHaveLength(7);
  expect(report.declarations).toContain("Cycle25Verification.plainMoment");
  expect(report.kernels).toEqual(["Lean default", "nanoda", "con-ron"]);
  expect(report.statement_definitions_compared).toBe(true);
  const independent = page.getByRole("link", {
    name: "Independent maintainer replay receipt",
    exact: true,
  });
  const receipt = await (
    await request.get((await independent.getAttribute("href")) as string)
  ).json();
  expect(receipt.status).toBe("PASS");
  expect(receipt.source_commit).toBe(
    "58344dfdbe756cf2f743da1908ffe0582418cf5b",
  );
  expect(receipt.theta_exact).toBe("683505193/781250000");
  expect(receipt.targets).toHaveLength(8);
  expect(receipt.targets).toContain("QRHBoundsPR9.quarticRootExistsUnique");
  expect(receipt.candidate_modules_rebuilt).toBe(3224);
  expect(receipt.challenge_exported_before_candidate_execution).toBe(true);
  expect(receipt.receipt_outside_candidate).toBe(true);
  await expect(page.locator(".proof-detail")).toContainText(
    "akashlevy-20261009-weighted-numerator",
  );
  const catalogue = await (await request.get("/catalogue.json")).json();
  const record = catalogue.records.find(
    (r: { id: string }) => r.id === "cycle25-quartic-20261010",
  );
  expect(record.timeline_at).toBe(receipt.verified_at);
  expect(record.first_verified_at).toBe(receipt.verified_at);
  expect(record.submitted_at).toBe("2026-10-10T12:08:27Z");
  expect(record.published_at).toBe("");
  expect(record.merged_at).toBe("");
  const pdfLink = page.getByRole("link", { name: "Paper (PDF)", exact: true });
  const pdf = await request.get((await pdfLink.getAttribute("href")) as string);
  expect(pdf.ok()).toBe(true);
  expect(pdf.headers()["content-type"]).toContain("application/pdf");
  expect((await pdf.body()).subarray(0, 5).toString()).toBe("%PDF-");
  const texLink = page.getByRole("link", {
    name: "Paper source (TeX)",
    exact: true,
  });
  const tex = await request.get((await texLink.getAttribute("href")) as string);
  expect(tex.ok()).toBe(true);
  expect(await tex.text()).toContain("\\documentclass");
});
const chartFixtures = () =>
  JSON.parse(
    readFileSync(
      new URL("../fixtures/chart-records.json", import.meta.url),
      "utf8",
    ),
  );
test("Akash Levy details expose the independently checked source and receipt", async ({
  page,
  request,
}) => {
  await page.goto("/");
  await page
    .getByRole("button", {
      name: "Akash Levy · weighted numerator",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("10499/12000");
  await expect(page.locator(".proof-detail")).toContainText(
    "Verified in our framework",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "independently rebuilt",
  );
  const link = page.getByRole("link", {
    name: "Independent maintainer replay receipt",
    exact: true,
  });
  await expect(link).toHaveAttribute(
    "href",
    "/proofs/akashlevy-20261010-safe-replay/result.json",
  );
  const response = await request.get(
    (await link.getAttribute("href")) as string,
  );
  expect(response.ok()).toBe(true);
  const receipt = await response.json();
  expect(receipt.status).toBe("PASS");
  expect(receipt.theta_exact).toBe("10499/12000");
  expect(receipt.source_commit).toBe(
    "ec626ec9c0e7ab7b29f6c916314932caeb4df39a",
  );
  expect(receipt.candidate_modules_rebuilt).toBe(2898);
  expect(receipt.kernels).toEqual(["Lean default", "nanoda", "con-ron"]);
  expect(receipt.challenge_exported_before_candidate_execution).toBe(true);
  expect(receipt.receipt_outside_candidate).toBe(true);
  const catalogue = await (await request.get("/catalogue.json")).json();
  const record = catalogue.records.find(
    (r: { id: string }) => r.id === "akashlevy-20261009-weighted-numerator",
  );
  expect(record.first_verified_at).toBe(receipt.verified_at);
  expect(record.timeline_at).toBe(receipt.verified_at);
});
test("Argonaut details link the isolated maintainer receipt and preserve its exact bound", async ({
  page,
  request,
}) => {
  await page.goto("/");
  await page
    .getByRole("button", { name: "Argonaut · perturbed boundary", exact: true })
    .click();
  await expect(page.locator(".proof-detail")).toContainText("3499999/4000000");
  await expect(page.locator(".proof-detail")).toContainText(
    "Verified in our framework",
  );
  const link = page.getByRole("link", {
    name: "Independent maintainer replay receipt",
    exact: true,
  });
  await expect(link).toHaveAttribute(
    "href",
    "/proofs/argonaut-20261010-safe-replay/result.json",
  );
  const response = await request.get(
    (await link.getAttribute("href")) as string,
  );
  expect(response.ok()).toBe(true);
  const receipt = await response.json();
  expect(receipt.status).toBe("PASS");
  expect(receipt.theta_exact).toBe("3499999/4000000");
  expect(receipt.kernels).toEqual(["Lean default", "nanoda", "con-ron"]);
  expect(receipt.challenge_exported_before_candidate_execution).toBe(true);
  expect(receipt.receipt_outside_candidate).toBe(true);
  await expect(
    page.getByRole("link", {
      name: "Sandboxed reproduction instructions",
      exact: true,
    }),
  ).toBeVisible();
});
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
test("current results, verification statuses and source downloads", async ({
  page,
  request,
}, info) => {
  await page.goto("/");
  await expect(page.locator("tbody tr")).toHaveCount(liveRecords.length);
  await expect(page.locator("[data-dot]")).toHaveCount(liveRecords.length);
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
  await expect(
    page.getByRole("button", {
      name: "Nielstron · compressed rational refinement",
      exact: true,
    }),
  ).toHaveCount(0);
  const native = await request.get(
    "/proofs/nielstron-20261009-tightening/native-lean-verification.json",
  );
  expect(native.ok()).toBeTruthy();
  const nativeReport = await native.json();
  expect(nativeReport.status).toBe("PASS");
  expect(nativeReport.external_checker_status).toContain("Not checked");
  const independent = await request.get(
    "/proofs/nielstron-20261009-kernels/result.json",
  );
  expect(independent.ok()).toBeTruthy();
  const independentReport = await independent.json();
  expect(independentReport.status).toBe("PASS");
  expect(independentReport.kernels).toEqual([
    "Lean default",
    "nanoda",
    "con-ron",
  ]);
  expect(independentReport.source_commit).toBe(
    "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6",
  );
  await page
    .getByRole("button", {
      name: "Nielstron · exact algebraic endpoint",
      exact: true,
    })
    .click();
  await expect(page.locator(".proof-detail")).toContainText(
    "Verified in our framework",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "874957019420098946128603850561452983/1000000000000000000000000000000000000",
  );
  await expect(page.locator(".proof-detail")).toContainText(
    "657e³−954e²+21e+20=0",
  );
  await expect(page.locator(".proof-detail")).not.toContainText(
    "Signed verification receipt",
  );
  const algebraic = await request.get(
    "/proofs/nielstron-algebraic-20261009-kernels/result.json",
  );
  expect(algebraic.ok()).toBeTruthy();
  const algebraicReport = await algebraic.json();
  expect(algebraicReport.status).toBe("PASS");
  expect(algebraicReport.declarations).toHaveLength(7);
  expect(algebraicReport.declarations).toContain("QRHPalomar.existsUniqueRoot");
  expect(algebraicReport.kernels).toEqual([
    "Lean default",
    "nanoda",
    "con-ron",
  ]);
  expect(algebraicReport.source_commit).toBe(
    "2fc2b0b7f2b9510df4618936e1b2ccd58f7d9171",
  );
  expect(algebraicReport.signed_admission).toBe(false);
  const catalogue = await (await request.get("/catalogue.json")).json();
  const current = catalogue.records.filter((r: { id: string }) =>
    r.id.startsWith("nielstron-"),
  );
  expect(current).toHaveLength(1);
  expect(current[0].id).toBe("nielstron-20261009-tightening");
  expect(current[0].proof_revision).toBe("nielstron-algebraic-20261009");
  expect(catalogue.historical_records).toHaveLength(1);
  await expect(
    page.getByRole("link", {
      name: "Previous N24 independent kernel report (historical revision)",
    }),
  ).toBeVisible();
  const reg = await (await request.get("/registry.json")).json();
  expect(reg.records).toEqual([]);
  await page.getByRole("button", { name: "Close proof details" }).click();
  await page.evaluate(() => window.scrollTo(0, 0));
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-live.png`,
    fullPage: true,
  });
});
test("selection, exact sorting and zoom", async ({ page }, info) => {
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
  await expect(page.locator("tbody tr").first()).toContainText(
    "quartic boundary",
  );
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect(page.locator("tbody tr").first()).toContainText("seven eighths");
  await page
    .getByRole("button", { name: "Exact bound θ", exact: true })
    .click();
  await expect(page.locator("tbody tr").first()).toContainText(
    "quartic boundary",
  );
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
  await expect(page.locator("[data-dot]")).toHaveCount(verifiedCount);
  const before = await page.locator(".verified-frontier").getAttribute("d");
  const best = await page.locator(".best-bound").textContent();
  const pending = {
    ...liveRecords.find(
      (r: { id: string }) => r.id === "cycle25-quartic-20261010",
    ),
    id: "pending-test-only",
    title: "Pending test contribution",
    status: "verification-pending",
    first_verified_at: "",
    builds_on: [],
    theta: { numerator: "1", denominator: "2" },
    timeline_at: "2026-10-11T00:00:00Z",
    date_label: "Submitted",
  };
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({
      json: {
        schema_version: 1,
        records: [...liveRecords, pending],
      },
    }),
  );
  await page.reload();
  await expect(page.locator("tbody tr")).toHaveCount(liveRecords.length + 1);
  await expect(page.locator("[data-dot]")).toHaveCount(verifiedCount);
  await expect(page.locator('[data-id="pending-test-only"]')).toHaveCount(0);
  await expect(page.locator(".best-bound")).toHaveText(best!);
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
