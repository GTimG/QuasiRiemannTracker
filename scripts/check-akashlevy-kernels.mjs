import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { validateAkashlevyKernelEvidence } from "../core/akashlevy-kernel-evidence.mjs";
const root = resolve(process.argv[2] || ".");
const catalogue = JSON.parse(
  readFileSync(process.argv[3] || `${root}/catalogue/results.json`, "utf8"),
);
const report = validateAkashlevyKernelEvidence(root, catalogue);
console.log(
  report
    ? "Independent Akash Levy receipt and complete proof source authenticated."
    : "Akash Levy contribution remains pending independent verification.",
);
