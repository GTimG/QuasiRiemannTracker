import { spawn } from "node:child_process";
import { chromium } from "playwright";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { get } from "node:http";

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
  await page.waitForFunction(
    () => document.querySelectorAll("[data-dot]").length === 6,
  );
  assert.equal(await page.locator("tbody tr").count(), 6);
  for (const name of [
    "registry.json",
    "catalogue.json",
    "site.json",
    "favicon.svg",
    "proofs/qrh-20261009/Nonvanishing.lean",
    "proofs/qrh-20261009/verification.json",
    "proofs/qrh-20261009/SHA256SUMS.txt",
    "proofs/nielstron-20261009-tightening/native-lean-verification.json",
    "proofs/nielstron-20261009-tightening/TighterNonvanishing.lean",
    "proofs/nielstron-20261009-tightening/collection.json",
    "proofs/nielstron-20261009-kernels/result.json",
    "proofs/nielstron-20261009-kernels/control-results.json",
    "proofs/nielstron-20261009-kernels/collection.json",
    "proofs/nielstron-algebraic-20261009/collection.json",
    "proofs/nielstron-algebraic-20261009/native-final-audit.json",
    "proofs/nielstron-algebraic-20261009/token-counts.json",
    "proofs/nielstron-algebraic-20261009-kernels/result.json",
    "proofs/nielstron-algebraic-20261009-kernels/control-results.json",
    "proofs/nielstron-algebraic-20261009-kernels/collection.json",
    "proofs/single-prime-29-33-20261010/multi-kernel-report.json",
    "proofs/single-prime-29-33-20261010/SHA256SUMS.txt",
    "proofs/single-prime-29-33-20261010/zeta_zero_free_4_33_self_contained.pdf",
  ]) {
    const response = await page.request.get(origin + base + name);
    assert.equal(response.status(), 200, name);
    if (name.endsWith(".json")) await response.json();
    if (name.endsWith(".pdf"))
      assert.equal((await response.body()).subarray(0, 5).toString(), "%PDF-");
  }
  for (const id of [
    "qrh-20261009",
    "nielstron-algebraic-20261009",
    "single-prime-29-33-20261010",
  ]) {
    const proofBase = origin + base + `proofs/${id}/`;
    const checksum = await (await page.request.get(proofBase + "SHA256SUMS.txt")).text();
    const [digest, archiveName] = checksum.trim().split("  ");
    assert.equal(archiveName, "source-public.tar.gz");
    // Read wire bytes: browser clients transparently decode Vite's gzip response.
    const archive = await new Promise((resolve, reject) => {
      const request = get(proofBase + archiveName, (response) => {
        if (response.statusCode !== 200) return reject(Error("Archive unavailable"));
        const chunks = [];
        response.on("data", (chunk) => chunks.push(chunk));
        response.on("error", reject);
        response.on("end", () => resolve(Buffer.concat(chunks)));
      });
      request.on("error", reject);
      request.setTimeout(30000, () => request.destroy(Error("Archive download timed out")));
    });
    assert.equal(createHash("sha256").update(archive).digest("hex"), digest);
  }
  const proofBase = origin + base + "proofs/qrh-20261009/";
  const retired = await page.request.get(proofBase + "source.tar.gz");
  assert.notDeepEqual((await retired.body()).subarray(0, 2), Buffer.from([0x1f, 0x8b]));
  await page
    .getByRole("button", {
      name: "ProofCouncil · certified uniform descent",
      exact: true,
    })
    .click();
  const link = page.getByRole("link", {
    name: "Lean proof source",
    exact: false,
  });
  assert.equal(
    await link.getAttribute("href"),
    base + "proofs/qrh-20261009/Nonvanishing.lean",
  );
  assert.deepEqual(failures, []);
  console.log(
    `PASS: production build at ${base}, six dots, JSON, favicon and proof evidence paths; no browser errors.`,
  );
} finally {
  if (browser) await browser.close();
  server.kill("SIGTERM");
}
