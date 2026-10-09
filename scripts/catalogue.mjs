import { readFileSync, writeFileSync, existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { validateCatalogue } from "../core/catalogue.mjs";
import { validateNativeKernelEvidence } from "../core/native-kernel-evidence.mjs";

const data = validateCatalogue(
  JSON.parse(readFileSync("catalogue/results.json", "utf8")),
);
validateNativeKernelEvidence(process.cwd(), data);
const proof = "proofs/qrh-20261009/";
const sha = (p) => createHash("sha256").update(readFileSync(p)).digest("hex");
const manifest = JSON.parse(
  readFileSync("proofs/qrh-20261009.sha256.json", "utf8"),
);
for (const [path, digest] of Object.entries(manifest)) {
  if (
    path.startsWith("/") ||
    path.split("/").includes("..") ||
    sha(proof + path) !== digest
  )
    throw Error(`Proof snapshot changed: ${path}`);
}
const audit = JSON.parse(
  readFileSync(proof + "audit/final-verification.json", "utf8"),
);
const recheck = JSON.parse(
  readFileSync(proof + "audit/operator-final-recheck.json", "utf8"),
);
if (
  audit.status !== "PASS" ||
  !audit.exact_three_targets_proved ||
  !recheck.success ||
  audit.source_sha256 !== sha(proof + audit.source) ||
  audit.threshold !== "874957019421/1000000000000"
)
  throw Error("Missing or mismatched framework evidence");
for (const ax of Object.values(audit.declarations))
  if (
    ax.some((a) => !["propext", "Classical.choice", "Quot.sound"].includes(a))
  )
    throw Error("Unexpected axiom");
for (const r of data.records)
  for (const ref of r.references)
    if (!ref.url.startsWith("https://") && !existsSync("public/" + ref.url))
      throw Error(`Missing public evidence: ${ref.url}`);
// Retained local kernel checks are evidence, separate from signed admission.
const checkRoot = "public/proofs/palomar-20261009/";
const checks = JSON.parse(readFileSync(checkRoot + "collection.json", "utf8"));
for (const [path, digest] of Object.entries(checks.files)) {
  if (
    path.startsWith("/") ||
    path.split("/").includes("..") ||
    sha(checkRoot + path) !== digest
  )
    throw Error(`Kernel-check evidence changed: ${path}`);
}
for (const [id, directory] of [
  ["openai-baseline", "openai"],
  ["proofcouncil-20261009", "qrh"],
]) {
  const record = data.records.find((r) => r.id === id);
  const report = JSON.parse(
    readFileSync(checkRoot + directory + "/result.json", "utf8"),
  );
  const config = JSON.parse(
    readFileSync(checkRoot + directory + "/comparator.json", "utf8"),
  );
  if (
    !record ||
    report.status !== "PASS" ||
    report.theta !== `${record.theta.numerator}/${record.theta.denominator}` ||
    report.palomar_preflight !== "passed" ||
    report.statement_definitions_compared !== true ||
    JSON.stringify(report.kernels) !==
      JSON.stringify(["Lean default", "nanoda", "con-ron"]) ||
    JSON.stringify([...report.allowed_axioms].sort()) !==
      JSON.stringify(["Classical.choice", "Quot.sound", "propext"]) ||
    JSON.stringify(report.declarations) !==
      JSON.stringify([
        "QRHPalomar.allDirichlet",
        "QRHPalomar.zeta",
        "QRHPalomar.allHecke",
      ]) ||
    JSON.stringify(config.theorem_names) !==
      JSON.stringify(report.declarations) ||
    config.definition_names.length !== 0
  )
    throw Error(`Incomplete kernel-check report: ${id}`);
  for (const [path, digest] of Object.entries(report.artifacts)) {
    if (
      !path.startsWith("exports/") &&
      sha(checkRoot + directory + "/" + path) !== digest
    )
      throw Error(`Kernel-check artifact changed: ${directory}/${path}`);
  }
  if (directory === "qrh" && report.proof_source_sha256 !== audit.source_sha256)
    throw Error(
      "Independent check does not match the accepted ProofCouncil source",
    );
}
const config = JSON.parse(readFileSync("site.config.json", "utf8"));
const repository = config.repository || process.env.GITHUB_REPOSITORY || null;
if (repository && !/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repository))
  throw Error("Invalid repository");
writeFileSync("public/catalogue.json", JSON.stringify(data, null, 2) + "\n");
writeFileSync(
  "public/site.json",
  JSON.stringify({ ...config, repository }, null, 2) + "\n",
);
console.log(
  `Catalogue: ${data.records.length} results; ${Object.keys(manifest).length} proof snapshot files authenticated. No signed registry receipts created.`,
);
