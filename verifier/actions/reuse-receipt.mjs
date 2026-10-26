// Source preparation and this validator run from github.workflow_sha, before
// any candidate elaboration or cache access, with only read-only permissions.
import { readFileSync, writeFileSync, appendFileSync } from "node:fs";
import { reusableReceipt, sourceContractDigest } from "../receipt-reuse.mjs";
import { sha256 } from "../common.mjs";
const { expected } = JSON.parse(
  readFileSync("verification-context/context.json", "utf8"),
);
try {
  const prepared = JSON.parse(
    readFileSync("verification/prepared/contract.json", "utf8"),
  );
  const verified = reusableReceipt(process.cwd(), expected, { prepared });
  if (verified) {
    writeFileSync(
      "verification/attempt.json",
      JSON.stringify(
        {
          ...expected,
          status: "registered",
          registration_sha256: sha256(verified.registration),
          source_contract_sha256: sourceContractDigest(prepared),
        },
        null,
        2,
      ) + "\n",
    );
    console.log(
      `Authenticated registered proof for ${expected.result_id}; no proof replay needed.`,
    );
  } else
    console.log(
      "No approved reusable receipt; run isolated proof verification.",
    );
  appendFileSync(process.env.GITHUB_OUTPUT, `reused=${Boolean(verified)}\n`);
} catch (error) {
  writeFileSync(
    "verification/attempt.json",
    JSON.stringify(
      { ...expected, status: "invalid-receipt", reason: error.message },
      null,
      2,
    ) + "\n",
  );
  throw error;
}
