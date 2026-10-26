import { spawn } from "node:child_process";
import { chromium } from "playwright";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { cmp } from "../core/rational.mjs";
const records = JSON.parse(
  readFileSync("catalogue/results.json", "utf8"),
).records;
const verified = records.filter((r) =>
  ["verified", "framework-verified"].includes(r.status),
);
const best = [...verified].sort((a, b) => cmp(a.theta, b.theta))[0];
const plottedCount = records.filter((r) =>
  ["verified", "framework-verified", "historical-baseline"].includes(r.status),
).length;

const base = process.env.QRH_BASE_PATH || "/qrh-bounds/";
const origin = "http://127.0.0.1:4184";
const server = spawn(
  process.execPath,
  [
    "node_modules/vite/bin/vite.js",
    "preview",
    "--host",
    "127.0.0.1",
    "--port",
    "4184",
    "--strictPort",
  ],
  {
    env: { ...process.env, QRH_BASE_PATH: base },
    stdio: ["ignore", "pipe", "pipe"],
  },
);
let serverError;
let serverOutput = "";
server.on("error", (error) => {
  serverError = error;
});
for (const stream of [server.stdout, server.stderr]) {
  stream.on("data", (chunk) => {
    serverOutput = (serverOutput + chunk.toString()).slice(-5000);
  });
}
let browser;
try {
  // Readiness is an HTTP response, independent of Vite's terminal output.
  const deadline = Date.now() + 30000;
  while (true) {
    if (serverError) throw serverError;
    if (server.exitCode !== null || server.signalCode !== null)
      throw Error(
        `Preview exited ${server.exitCode ?? server.signalCode}: ${serverOutput}`,
      );
    try {
      const response = await fetch(origin + base, {
        signal: AbortSignal.timeout(1000),
      });
      await response.body?.cancel();
      if (response.ok) break;
    } catch {
      // Connection refusal is expected while the preview server starts.
    }
    if (Date.now() >= deadline) {
      throw Error(
        `Preview did not respond at ${origin + base}: ${serverOutput}`,
      );
    }
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  browser = await chromium.launch();
  const page = await browser.newPage();
  const failures = [];
  page.on("pageerror", (e) => failures.push(e.message));
  page.on("response", (r) => {
    if (r.status() >= 400) failures.push(`${r.status()} ${r.url()}`);
  });
  await page.goto(origin + base);
  await page.locator(`[data-dot][data-id="${best.id}"]`).waitFor();
  await page.getByRole("button", { name: "Fit leaderboard", exact: true }).click();
  await page.waitForFunction(
    (count) => document.querySelectorAll("[data-dot]").length === count,
    plottedCount,
  );
  assert.equal(
    await page
      .getByRole("list", { name: "Contributions", exact: true })
      .getByRole("listitem")
      .count(),
    records.length,
  );
  for (const name of [
    "catalogue.json",
    "site.json",
    "favicon.svg",
    ...verified.map((r) => r.certificate_url),
  ]) {
    const response = await page.request.get(origin + base + name);
    assert.equal(response.status(), 200, name);
    if (name.endsWith(".json")) await response.json();
  }
  for (const record of verified) {
    assert.match(
      record.solution_url,
      /^https:\/\/github\.com\/[^/]+\/[^/]+\/blob\/[a-f0-9]{40}\/.+\.lean$/,
    );
  }
  assert.deepEqual(failures, []);
  console.log(
    `PASS: production build at ${base}, ${plottedCount} full-history points, JSON, favicon and verification records; no browser errors.`,
  );
} finally {
  if (browser) await browser.close();
  server.kill("SIGTERM");
}
