// Independent maintainer acceptance is separate from the author's historical report.
import { readFileSync, readdirSync, lstatSync } from "node:fs";
import { createHash } from "node:crypto";
import { join } from "node:path";
import { validateMaintainerReplay } from "./maintainer-replay.mjs";

export const AKASHLEVY_ID = "akashlevy-20261009-weighted-numerator";
export const AKASHLEVY_PIN = JSON.parse(
  readFileSync(
    new URL("./akashlevy-kernel-pins.json", import.meta.url),
    "utf8",
  ),
);
const sha = (data) => createHash("sha256").update(data).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const demand = (ok, message) => {
  if (!ok) throw Error(`Akash Levy verification: ${message}`);
};

export function validateAkashlevyKernelEvidence(
  root,
  catalogue,
  pin = AKASHLEVY_PIN,
) {
  const records = catalogue.records.filter((r) => r.id === AKASHLEVY_ID);
  demand(records.length === 1, "missing or duplicate contribution");
  const record = records[0];
  if (record.status === "verification-pending") {
    demand(
      record.first_verified_at === "",
      "pending contribution has a verification date",
    );
    return null;
  }
  demand(
    record.status === "framework-verified" &&
      pin?.replay_profile === "akashlevy-weighted-v1",
    "independent sandboxed acceptance is required",
  );
  const inputs = JSON.parse(
    readFileSync(join(root, "verifier/akashlevy/pins.json")),
  );
  demand(
    record.repository === "akashlevy/QuasiRiemannTracker" &&
      record.source_commit === inputs.source_commit &&
      record.pr === 6,
    "source revision differs",
  );
  demand(
    `${record.theta.numerator}/${record.theta.denominator}` ===
      inputs.theta_exact && inputs.theta_exact === "10499/12000",
    "exact bound differs",
  );
  demand(
    same(record.entrypoint, {
      module: "WeightedQRH.Statements",
      declaration:
        "OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re",
    }),
    "entrypoint differs",
  );
  const proof = join(root, "proofs", AKASHLEVY_ID);
  for (const path of [join(root, "proofs"), proof])
    demand(!lstatSync(path).isSymbolicLink(), "unsafe source prefix");
  const files = [];
  function walk(prefix = "") {
    for (const name of readdirSync(join(proof, prefix)).sort()) {
      demand(/^[A-Za-z0-9_.-]+$/.test(name), "unsafe source path");
      const path = prefix ? `${prefix}/${name}` : name;
      const stat = lstatSync(join(proof, path));
      demand(!stat.isSymbolicLink(), "source symlink");
      if (stat.isDirectory()) walk(path);
      else {
        demand(
          stat.isFile() && stat.size <= 12 * 1024 ** 2,
          "unsafe source file",
        );
        files.push(path);
      }
    }
  }
  walk();
  demand(
    same(files.sort(), Object.keys(inputs.submission_files).sort()),
    "checked source inventory changed",
  );
  for (const path of files)
    demand(
      sha(readFileSync(join(proof, path))) === inputs.submission_files[path],
      `checked source changed: ${path}; re-verification required`,
    );
  const report = validateMaintainerReplay(root, pin, {
    source_commit: record.source_commit,
    repository: record.repository,
    source_compiler: "4.34.1",
    judge_toolchain: "4.35.0-rc2",
    palomar_commit: "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44",
  });
  demand(
    record.first_verified_at === report.first_verified_at &&
      record.timeline_at === report.first_verified_at,
    "timeline must use the first independent acceptance",
  );
  demand(
    record.references.some(
      (r) => r.url === `${pin.directory.replace(/^public\//, "")}/result.json`,
    ),
    "independent receipt link missing",
  );
  return report;
}
