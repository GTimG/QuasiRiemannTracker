import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { validateAlgebraicKernelEvidence } from "../core/algebraic-kernel-evidence.mjs";

const args = process.argv.slice(2);
let root = fileURLToPath(new URL("../", import.meta.url));
let directory, cataloguePath, bindingPath;
while (args.length) {
  const flag = args.shift(), value = args.shift();
  if (!value) throw Error("Missing validation argument");
  if (flag === "--root") root = resolve(value);
  else if (flag === "--evidence-dir") directory = resolve(value);
  else if (flag === "--catalogue") cataloguePath = resolve(value);
  else if (flag === "--binding") bindingPath = resolve(value);
  else throw Error("Unknown validation argument: " + flag);
}
const report = validateAlgebraicKernelEvidence(root,
  JSON.parse(readFileSync(cataloguePath || resolve(root, "catalogue/results.json"))),
  directory, bindingPath ? JSON.parse(readFileSync(bindingPath)) : undefined);
console.log(report
  ? "Seven-target algebraic checker dossier authenticated; mathematical checks are the separate recorded run."
  : "No algebraic acceptance dossier; no external verification claimed.");
