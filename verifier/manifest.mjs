import { lstatSync, readdirSync, readFileSync, realpathSync } from "node:fs";
import path from "node:path";
import { rational } from "../core/rational.mjs";
import { sha256 } from "./common.mjs";

import { submissionDependencies } from "./submission-dependencies.mjs";
import { exactBound } from "../core/exact-bound.mjs";
export function manifest({ id, theta, exact_bound }) {
  if (!/^[a-z][a-z0-9-]{2,63}$/.test(id ?? ""))
    throw Error("Invalid submission ID");
  rational(theta.numerator, theta.denominator);
  if (BigInt(theta.numerator) <= 0n) throw Error("Bound must be positive");
  const { lean, ...bound } = exactBound(
    exact_bound ?? `${theta.numerator}/${theta.denominator}`,
  );
  return {
    id,
    ...bound,
    entrypoint: { module: "Candidate.Main", declaration: "Candidate.bound" },
  };
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
export function submissionFiles(dir) {
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
        if (
          file !== "src" &&
          !/^src\/(?:Candidate|Submissions)(?:\/[A-Za-z_][A-Za-z0-9_]*)*$/.test(
            file,
          )
        )
          throw Error("Unapproved directory");
        walk(file);
        continue;
      }
      if (
        file !== "metadata.json" &&
        !/^src\/(?:Candidate|Submissions)\/(?:[A-Za-z_][A-Za-z0-9_]*\/)*[A-Za-z_][A-Za-z0-9_]*\.lean$/.test(
          file,
        )
      )
        throw Error(
          "Submissions contain metadata.json and Lean source: " + file,
        );
      total += stat.size;
      if (
        total > 64 * 1024 * 1024 ||
        stat.size > 2 * 1024 * 1024 ||
        files.length >= 8192
      )
        throw Error("Submission size limit");
      const bytes = readFileSync(full);
      files.push({ path: file, sha256: sha256(bytes), bytes });
    }
  }
  walk();
  if (!files.some((f) => f.path === "src/Candidate/Main.lean"))
    throw Error("Missing src/Candidate/Main.lean");
  const metadataFile = files.find((f) => f.path === "metadata.json");
  if (!metadataFile) throw Error("Missing metadata.json");
  if (metadataFile.bytes.length > 65536)
    throw Error("Submission metadata is too large");
  submissionDependencies(JSON.parse(metadataFile.bytes.toString()));
  return {
    files,
    inventory: files.map(({ path, sha256 }) => ({ path, sha256 })),
  };
}

export function submission(dir, declaration) {
  return { ...submissionFiles(dir), manifest: manifest(declaration) };
}
