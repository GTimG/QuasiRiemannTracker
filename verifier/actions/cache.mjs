import { createHash } from "node:crypto";
import { appendFileSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";

const inputs = [
  "verifier/pins.json",
  "verifier/worker_resources.py",
  "verifier/standard/tool-pins.json",
  "verifier/standard/lakefile.lean",
  "verifier/standard/lake-manifest.json",
  "verifier/actions/setup.py",
  "verifier/actions/library_contract.py",
  "verifier/actions/patches/PrimeNumberTheoremAnd-lean4341.patch",
  "verifier/actions/patches/rellich-kondrachov-lean4341.patch",
  "verifier/actions/cache.mjs",
  ".github/actions/verifier-cache/action.yml",
];

export function cachePlan(root, { os, arch }) {
  if (os !== "Linux" || arch !== "X64")
    throw new Error("The pinned checking environment requires Linux X64");
  // The shared environment contains the pinned toolchains and package libraries.
  // Submission source and its outputs are handled by the confined build.
  const hash = createHash("sha256");
  for (const name of inputs) {
    hash.update(name + "\0");
    hash.update(readFileSync(resolve(root, name)));
    hash.update("\0");
  }
  return {
    key: `qrh-environment-v2-ubuntu24.04-${os}-${arch}-${hash.digest("hex")}`,
    path: "verification/environment",
  };
}

if (
  process.argv[1] &&
  resolve(process.argv[1]) === fileURLToPath(import.meta.url)
) {
  const plan = cachePlan(process.cwd(), {
    os: process.env.RUNNER_OS,
    arch: process.env.RUNNER_ARCH,
  });
  appendFileSync(
    process.env.GITHUB_OUTPUT,
    `key=${plan.key}\npath=${plan.path}\n`,
  );
  console.log(`Shared environment: ${plan.key}`);
}
