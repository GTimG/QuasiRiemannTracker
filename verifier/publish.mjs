import {
  readFileSync,
  readdirSync,
  writeFileSync,
  mkdtempSync,
  mkdirSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { firstSuccess } from "./history.mjs";
import { readJSON, sha256, envelope, iso } from "./common.mjs";
import { receipt, reviewed } from "./receipts.mjs";
import { inspectPR, materialize, reviews } from "./github.mjs";
const policy = readJSON("verifier/trust-policy.json"),
  signed = readJSON(process.argv[2] ?? "out/receipt.json"),
  r = receipt(signed, policy),
  source = await inspectPR(r.repository, r.pr),
  approval = reviewed(source, await reviews(r.repository, r.pr), policy);
const history = readdirSync("registry/verifications")
  .filter((f) => f.endsWith(".json"))
  .map((f) => readJSON("registry/verifications/" + f));
const first = firstSuccess(history, policy, r);
if (sha256(first.envelope) !== sha256(signed))
  throw Error(
    "Use the first successful archived verification receipt and its logs",
  );
if (source.head_sha !== r.source_commit)
  throw Error("PR source changed after verification");
const dir = mkdtempSync(path.join(tmpdir(), "qrh-publish-"));
try {
  const merged = await materialize(
    r.repository,
    source.merge_commit,
    source.id,
    dir,
  );
  receipt(signed, policy, {
    ...merged,
    source_commit: source.head_sha,
    repository: r.repository,
    pr: r.pr,
  });
  const log = readFileSync(process.argv[3] ?? "out/verification.log", "utf8");
  if (sha256(log) !== r.log_sha256) throw Error("Log mismatch");
  const p = {
    kind: "qrh-publication-v1",
    id: r.manifest.id,
    repository: r.repository,
    pr: r.pr,
    pr_author: source.author,
    source_commit: r.source_commit,
    content_digest: r.content_digest,
    receipt_sha256: sha256(signed),
    reviews: approval,
    submitted_at: source.submitted_at,
    merged_at: source.merged_at,
    published_at: iso(),
    merge_commit: source.merge_commit,
  };
  const publication = envelope(
    p,
    process.env.QRH_PUBLICATION_KEY,
    process.env.QRH_PUBLICATION_KEY_ID,
  );
  const out = path.join("out/publication", r.manifest.id);
  mkdirSync(out, { recursive: true });
  writeFileSync(
    path.join(out, "publication.json"),
    JSON.stringify(publication, null, 2) + "\n",
  );
  writeFileSync(
    path.join(out, "receipt.json"),
    JSON.stringify(signed, null, 2) + "\n",
  );
  writeFileSync(path.join(out, "verification.log"), log);
  console.log(
    "Signed publication bundle prepared for maintainer registry PR:",
    out,
  );
} finally {
  rmSync(dir, { recursive: true, force: true });
}
