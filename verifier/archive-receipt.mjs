import { readFileSync, writeFileSync, mkdirSync, existsSync } from "node:fs";
import { readJSON, sha256 } from "./common.mjs";
import { receipt } from "./receipts.mjs";
const signed = readJSON(process.argv[2]),
  policy = readJSON("verifier/trust-policy.json"),
  r = receipt(signed, policy),
  log = readFileSync(process.argv[3]);
if (sha256(log) !== r.log_sha256) throw Error("Log digest mismatch");
mkdirSync("registry/verifications", { recursive: true });
mkdirSync("registry/logs", { recursive: true });
const p = "registry/verifications/" + sha256(signed) + ".json",
  l = "registry/logs/" + r.log_sha256 + ".log";
if (existsSync(p)) throw Error("Receipt already archived");
writeFileSync(p, JSON.stringify(signed, null, 2) + "\n", { flag: "wx" });
if (!existsSync(l)) writeFileSync(l, log, { flag: "wx" });
console.log("Archived authenticated receipt:", p);
