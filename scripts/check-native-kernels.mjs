import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { validateNativeKernelEvidence } from "../core/native-kernel-evidence.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const args = process.argv.slice(2);
let directory,
  cataloguePath = resolve(root, "catalogue/results.json");
while (args.length) {
  const flag = args.shift(),
    value = args.shift();
  if (!value) throw Error("Missing validation argument");
  if (flag === "--evidence-dir") directory = resolve(value);
  else if (flag === "--catalogue") cataloguePath = resolve(value);
  else throw Error("Unknown validation argument: " + flag);
}
const report = validateNativeKernelEvidence(
  root,
  JSON.parse(readFileSync(cataloguePath)),
  directory,
);
console.log(
  report
    ? "Independent checker dossier authenticated; mathematical checking is a separate recorded run."
    : "No independent candidate acceptance dossier; catalogue remains pending.",
);
