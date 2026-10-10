import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { validateCycle25KernelEvidence } from "../core/cycle25-kernel-evidence.mjs";
const root = resolve(process.argv[2] || ".");
const catalogue = JSON.parse(
  readFileSync(process.argv[3] || `${root}/catalogue/results.json`, "utf8"),
);
const report = validateCycle25KernelEvidence(root, catalogue);
console.log(
  report
    ? "Independent Cycle25 receipt and complete proof source authenticated."
    : "Cycle25 contribution remains pending independent verification.",
);
