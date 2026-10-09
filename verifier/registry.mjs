import {
  readdirSync,
  readFileSync,
  mkdirSync,
  writeFileSync,
  existsSync,
} from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { readJSON, sha256 } from "./common.mjs";
import { receipt, publication, event } from "./receipts.mjs";
import { firstSuccess } from "./history.mjs";
import { recordHistory, activeRecords } from "../core/rational.mjs";
const ROOT = fileURLToPath(new URL("../", import.meta.url));
export function generateRegistry(bundles, eventRecords, policy, history = []) {
  const records = [],
    ids = new Set();
  for (const bundle of bundles) {
    const p = publication(bundle.publication, policy),
      r = receipt(bundle.receipt, policy);
    if (firstSuccess(history, policy, r).payload.verified_at !== r.verified_at)
      throw Error("Publication does not use first successful verification");
    if (
      p.receipt_sha256 !== sha256(bundle.receipt) ||
      p.source_commit !== r.source_commit ||
      p.content_digest !== r.content_digest ||
      p.id !== r.manifest.id ||
      p.pr !== r.pr
    )
      throw Error("Publication/receipt mismatch");
    if (sha256(bundle.log) !== r.log_sha256)
      throw Error("Missing or altered logs");
    if (ids.has(p.id)) throw Error("Immutable ID already published");
    ids.add(p.id);
    if (
      Date.parse(r.verified_at) > Date.parse(p.published_at) ||
      Date.parse(p.merged_at) > Date.parse(p.published_at) ||
      Date.parse(p.submitted_at) > Date.parse(r.verified_at)
    )
      throw Error("Inconsistent dates");
    records.push({
      ...r.manifest,
      source_commit: r.source_commit,
      repository: r.repository,
      pr: r.pr,
      first_verified_at: r.verified_at,
      submitted_at: p.submitted_at,
      published_at: p.published_at,
      merged_at: p.merged_at,
      receipt_digest: p.receipt_sha256,
      receipt_url: `/records/${p.id}/receipt.json`,
      log_url: `/records/${p.id}/verification.log`,
      status: "verified",
    });
  }
  for (const r of records)
    for (const parent of r.builds_on) {
      const predecessor = records.find((x) => x.id === parent);
      if (!predecessor || predecessor.first_verified_at >= r.first_verified_at)
        throw Error("Unknown, cyclic or later predecessor");
    }
  let previous = null,
    lastAt = null;
  const events = eventRecords.map((record) => {
    const e = event(record, policy);
    if (
      !ids.has(e.id) ||
      e.previous !== previous ||
      (e.replacement && !ids.has(e.replacement))
    )
      throw Error("Invalid event chain");
    if (
      (lastAt && e.at < lastAt) ||
      e.at < records.find((r) => r.id === e.id).first_verified_at
    )
      throw Error("Events must be chronologically valid");
    lastAt = e.at;
    previous = sha256(record);
    return e;
  });
  const ranked = recordHistory(records, events);
  return {
    schema_version: 1,
    verification_policy: "comparator-and-nanoda-v1",
    records: ranked,
    events,
    active_ids: activeRecords(records, events).map((r) => r.id),
    baseline_status: records.some((r) => r.id === "openai-baseline")
      ? "verified"
      : "infrastructure-blocked",
  };
}
export function buildRegistry() {
  const policy = readJSON(path.join(ROOT, "verifier/trust-policy.json"));
  const dirs = readdirSync(path.join(ROOT, "registry/records"), {
    withFileTypes: true,
  }).filter((d) => d.isDirectory());
  const bundles = dirs.map((d) => {
    const p = path.join(ROOT, "registry/records", d.name);
    return {
      receipt: readJSON(path.join(p, "receipt.json")),
      publication: readJSON(path.join(p, "publication.json")),
      log: readFileSync(path.join(p, "verification.log"), "utf8"),
    };
  });
  const events = readdirSync(path.join(ROOT, "registry/events"))
    .filter((p) => p.endsWith(".json"))
    .sort()
    .map((p) => readJSON(path.join(ROOT, "registry/events", p)));
  const history = readdirSync(path.join(ROOT, "registry/verifications"))
    .filter((p) => p.endsWith(".json"))
    .map((p) => readJSON(path.join(ROOT, "registry/verifications", p)));
  for (const r of history) {
    receipt(r, policy);
    if (
      !existsSync(
        path.join(ROOT, "registry/logs", r.payload.log_sha256 + ".log"),
      ) ||
      sha256(
        readFileSync(
          path.join(ROOT, "registry/logs", r.payload.log_sha256 + ".log"),
        ),
      ) !== r.payload.log_sha256
    )
      throw Error("Missing or altered journal log");
    if (
      !existsSync(
        path.join(ROOT, "registry/verifications", sha256(r) + ".json"),
      )
    )
      throw Error("Journal receipt must be content-addressed");
  }
  const registry = generateRegistry(bundles, events, policy, history);
  mkdirSync(path.join(ROOT, "public"), { recursive: true });
  writeFileSync(
    path.join(ROOT, "public/registry.json"),
    JSON.stringify(registry, null, 2) + "\n",
  );
  for (const b of bundles) {
    const dest = path.join(
      ROOT,
      "public/records",
      b.receipt.payload.manifest.id,
    );
    mkdirSync(dest, { recursive: true });
    writeFileSync(
      path.join(dest, "receipt.json"),
      JSON.stringify(b.receipt, null, 2),
    );
    writeFileSync(
      path.join(dest, "publication.json"),
      JSON.stringify(b.publication, null, 2),
    );
    writeFileSync(path.join(dest, "verification.log"), b.log);
  }
  console.log(
    `Authenticated registry: ${registry.records.length} contributions, ${events.length} events.`,
  );
  return registry;
}
if (process.argv[1] === fileURLToPath(import.meta.url)) buildRegistry();
