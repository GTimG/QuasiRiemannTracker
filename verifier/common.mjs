import { createHash, sign, verify } from "node:crypto";
import { readFileSync } from "node:fs";
export function canonical(x) {
  if (x === null || typeof x !== "object") return JSON.stringify(x);
  if (Array.isArray(x)) return "[" + x.map(canonical).join(",") + "]";
  return (
    "{" +
    Object.keys(x)
      .sort()
      .map((k) => JSON.stringify(k) + ":" + canonical(x[k]))
      .join(",") +
    "}"
  );
}
export const sha256 = (x) =>
  createHash("sha256")
    .update(typeof x === "string" || Buffer.isBuffer(x) ? x : canonical(x))
    .digest("hex");
export const readJSON = (p) => JSON.parse(readFileSync(p, "utf8"));
export const pins = readJSON(new URL("./pins.json", import.meta.url));
export const PIN_DIGEST = sha256(pins);
export function envelope(payload, key, keyId) {
  return {
    payload,
    key_id: keyId,
    signature: sign(null, Buffer.from(canonical(payload)), key).toString(
      "base64",
    ),
  };
}
export function authenticate(record, keys) {
  if (
    !record ||
    Object.keys(record).sort().join() !== "key_id,payload,signature" ||
    typeof record.signature !== "string"
  )
    throw Error("Invalid signed envelope");
  const key = keys[record.key_id];
  if (
    !key ||
    !verify(
      null,
      Buffer.from(canonical(record.payload)),
      key,
      Buffer.from(record.signature, "base64"),
    )
  )
    throw Error("Unauthenticated record");
  return record.payload;
}
export const iso = () => new Date().toISOString();
