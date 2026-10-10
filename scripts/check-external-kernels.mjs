import { readFileSync } from "node:fs";
import { validateExternalKernelEvidence } from "../core/external-kernel-evidence.mjs";

const catalogue = JSON.parse(readFileSync("catalogue/results.json", "utf8"));
const reports = validateExternalKernelEvidence(process.cwd(), catalogue);
console.log(
  `External checker evidence: ${reports.length} reviewed dossiers authenticated; no signed receipts created.`,
);
