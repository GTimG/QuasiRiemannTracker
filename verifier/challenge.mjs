import { standardChallenge } from "../core/standard-challenge.mjs";
import { RATIONAL_DECLARATION } from "../core/exact-bound.mjs";
import { manifest } from "./manifest.mjs";
export const THEOREM = "QRH.canonical_bound";
export function challenge(m) {
  return standardChallenge(manifest(m).theta_exact);
}
export function solutionWrapper(m) {
  m = manifest(m);
  const proofs = [
    `  exact ${m.entrypoint.declaration} χ hs hpole`,
    ...(m.targets.length > 1 ? [`  exact ${RATIONAL_DECLARATION}`] : []),
  ];
  let body = challenge(m).replace("import Mathlib\n", "");
  for (const proof of proofs) body = body.replace("  sorry", proof);
  if (body.includes("sorry")) throw Error("Unfilled challenge theorem");
  return `import ${m.entrypoint.module}\n\n${body}`;
}
