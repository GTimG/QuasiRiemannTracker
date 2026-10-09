import { mkdirSync, writeFileSync } from "node:fs";
import { parseArgs } from "node:util";
import path from "node:path";
import { check } from "./runner.mjs";
const { values, positionals } = parseArgs({
  allowPositionals: true,
  options: {
    image: { type: "string" },
    out: { type: "string", default: "evidence/baseline-attempt" },
    "source-commit": { type: "string" },
    repository: { type: "string" },
    pr: { type: "string" },
    "orchestrator-commit": { type: "string" },
  },
});
try {
  const result = await check(positionals[0] ?? "submissions/openai-baseline", {
    image: values.image,
    sourceCommit: values["source-commit"],
    repository: values.repository,
    pr: values.pr ? Number(values.pr) : undefined,
    orchestratorCommit: values["orchestrator-commit"],
  });
  mkdirSync(values.out, { recursive: true });
  const { log, ...report } = result;
  writeFileSync(
    path.join(values.out, "attempt.json"),
    JSON.stringify(report, null, 2) + "\n",
  );
  writeFileSync(path.join(values.out, "verification.log"), log);
  console.log(result.status + ": " + (result.reason ?? "See retained logs."));
  process.exitCode =
    result.status === "accepted"
      ? 0
      : result.status === "infrastructure-blocked"
        ? 78
        : 1;
} catch (e) {
  console.error(e.message);
  process.exitCode = 2;
}
