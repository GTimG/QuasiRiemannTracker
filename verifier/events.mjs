import { readdirSync, writeFileSync } from "node:fs";
import { readJSON, sha256, envelope, iso } from "./common.mjs";
import { event } from "./receipts.mjs";
// Maintainer-only, offline signing. Evidence stays append-only; never mutate a contribution.
const [type, id, reason, replacement] = process.argv.slice(2),
  policy = readJSON("verifier/trust-policy.json");
const files = readdirSync("registry/events")
  .filter((f) => f.endsWith(".json"))
  .sort();
const last = files.at(-1);
const payload = {
  kind: "qrh-event-v1",
  type,
  id,
  reason,
  at: iso(),
  replacement: replacement ?? null,
  reviewer: process.env.QRH_REVIEWER,
  previous: last ? sha256(readJSON("registry/events/" + last)) : null,
};
const signed = envelope(
  payload,
  process.env.QRH_PUBLICATION_KEY,
  process.env.QRH_PUBLICATION_KEY_ID,
);
event(signed, policy);
const dest = `registry/events/${String(files.length + 1).padStart(6, "0")}-${sha256(signed)}.json`;
writeFileSync(dest, JSON.stringify(signed, null, 2) + "\n", { flag: "wx" });
console.log(dest);
