import { readFileSync } from "node:fs";
import { manifest } from "./manifest.mjs";
import { pins, sha256 } from "./common.mjs";
export const THEOREM = "QRH.canonical_bound";
export function challenge(m) {
  manifest(m);
  const template = readFileSync(
    new URL("./upstream-challenge.lean", import.meta.url),
    "utf8",
  );
  if (sha256(template) !== pins.challenge_sha256)
    throw Error("Trusted challenge template changed");
  // Replace ONLY the namespace/name and literal. No submitted syntax enters the statement.
  const n = m.theta.numerator.startsWith("-")
    ? `(${m.theta.numerator})`
    : m.theta.numerator;
  return template
    .replace("namespace OAI\n\nnamespace DirichletCharacter", "namespace QRH")
    .replace("LFunction_ne_zero_of_seven_eighths_lt_re", "canonical_bound")
    .replace("(7 / 8 : ℝ)", `(${n} / ${m.theta.denominator} : ℝ)`)
    .replace("end DirichletCharacter\n\nend OAI", "end QRH");
}
export function solutionWrapper(m) {
  manifest(m);
  return `import ${m.entrypoint.module}\n\n${challenge(m).replace("import Mathlib\n", "").replace("  sorry", `  exact ${m.entrypoint.declaration} χ hs hpole`)}`;
}
export function comparatorConfig() {
  return {
    challenge_module: "Challenge",
    solution_module: "Solution",
    theorem_names: [THEOREM],
    definition_names: [],
    permitted_axioms: pins.allowed_axioms,
    external_kernels: { nanoda: ["/opt/bin/nanoda_bin"] },
  };
}
