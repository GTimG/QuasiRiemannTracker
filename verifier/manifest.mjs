import Ajv from "ajv";
import { lstatSync, readdirSync, readFileSync, realpathSync } from "node:fs";
import path from "node:path";
import { rational, cmp, BASELINE } from "../core/rational.mjs";
import { readJSON, sha256 } from "./common.mjs";
const validate = new Ajv({ allErrors: true, strict: true }).compile(
  readJSON(new URL("../schemas/submission.schema.json", import.meta.url)),
);
export function manifest(input) {
  if (!validate(input))
    throw Error("Invalid manifest: " + JSON.stringify(validate.errors));
  rational(input.theta.numerator, input.theta.denominator);
  if (cmp(input.theta, BASELINE) > 0)
    throw Error("This track accepts bounds at most 7/8.");
  if (input.builds_on.includes(input.id))
    throw Error("A contribution cannot build on itself.");
  const inspect = (x) => {
    if (
      typeof x === "string" &&
      /[<>\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f\u202a-\u202e\u2066-\u2069]/u.test(
        x,
      )
    )
      throw Error("Unsafe metadata");
    if (x && typeof x === "object") Object.values(x).forEach(inspect);
  };
  inspect(input);
  for (const ref of [
    ...input.references,
    ...input.authors.filter((a) => a.url),
  ]) {
    const u = new URL(ref.url);
    if (u.protocol !== "https:" || u.username || u.password)
      throw Error("Unsafe URL");
  }
  return input;
}
export function safePath(p) {
  if (
    typeof p !== "string" ||
    !p ||
    p.length > 250 ||
    p.includes("\\") ||
    p.startsWith("/") ||
    p.split("/").some((x) => !x || x === "." || x === "..") ||
    !/^[A-Za-z0-9_./-]+$/.test(p)
  )
    throw Error("Unsafe path");
  return p;
}
export function submission(dir) {
  if (lstatSync(dir).isSymbolicLink()) throw Error("Symlink submission");
  const base = realpathSync(dir),
    files = [];
  let total = 0;
  function walk(rel = "") {
    for (const name of readdirSync(path.join(base, rel)).sort()) {
      const file = safePath(rel ? rel + "/" + name : name),
        full = path.join(base, file),
        stat = lstatSync(full);
      if (stat.isSymbolicLink() || (!stat.isFile() && !stat.isDirectory()))
        throw Error("Only regular files/directories allowed");
      if (stat.isDirectory()) {
        if (file !== "src" && !file.startsWith("src/Candidate"))
          throw Error("Unapproved directory");
        walk(file);
        continue;
      }
      if (
        !["manifest.json", "explanation.md", "LICENSE", "NOTICE"].includes(
          file,
        ) &&
        !/^src\/Candidate\/(?:[A-Z][A-Za-z0-9_]*\/)*[A-Z][A-Za-z0-9_]*\.lean$/.test(
          file,
        )
      )
        throw Error("Unapproved submission file: " + file);
      total += stat.size;
      if (
        total > 10 * 1024 * 1024 ||
        stat.size > 2 * 1024 * 1024 ||
        files.length >= 256
      )
        throw Error("Submission size limit");
      const bytes = readFileSync(full);
      files.push({ path: file, sha256: sha256(bytes), bytes });
    }
  }
  walk();
  const m = manifest(readJSON(path.join(base, "manifest.json")));
  const entry = "src/" + m.entrypoint.module.replaceAll(".", "/") + ".lean";
  if (
    !files.some((f) => f.path === entry) ||
    !files.some((f) => f.path === "explanation.md") ||
    !files.some((f) => f.path === "LICENSE")
  )
    throw Error("Missing source, explanation or license");
  const inventory = files.map(({ path, sha256 }) => ({ path, sha256 }));
  return {
    manifest: m,
    files,
    inventory,
    content_digest: sha256(inventory),
    manifest_digest: sha256(m),
  };
}
