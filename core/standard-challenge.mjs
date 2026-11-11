import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { exactBound } from "./exact-bound.mjs";
// The canonical statement at the exact bound and, for an algebraic bound, the
// rational upper bound that is ranked. Comparator checks every theorem here.
export function standardChallenge(theta_exact) {
  const bound = exactBound(theta_exact);
  const template = readFileSync(
    new URL("../verifier/upstream-challenge.lean", import.meta.url),
    "utf8",
  );
  const pins = JSON.parse(
    readFileSync(new URL("../verifier/pins.json", import.meta.url), "utf8"),
  );
  if (
    createHash("sha256").update(template).digest("hex") !==
    pins.challenge_sha256
  )
    throw Error("Trusted challenge template changed");
  const rationalBound = bound.rational_lean
    ? `theorem canonical_bound_le :\n    ((${bound.lean}) : ℝ) ≤ (${bound.rational_lean} : ℝ) := by\n  sorry\n\n`
    : "";
  return template
    .replace("namespace OAI\n\nnamespace DirichletCharacter", "namespace QRH")
    .replace("LFunction_ne_zero_of_seven_eighths_lt_re", "canonical_bound")
    .replace("(7 / 8 : ℝ)", `(${bound.lean} : ℝ)`)
    .replace("end DirichletCharacter\n\nend OAI", `${rationalBound}end QRH`);
}
