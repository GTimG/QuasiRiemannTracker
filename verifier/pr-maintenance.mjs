import {
  submissionDependencies,
  affectedSubmissions,
} from "./submission-dependencies.mjs";
// Candidate commits supply data; validators and worker code come from the base.
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { isDeepStrictEqual } from "node:util";
import { validateCatalogue, boundLabel } from "../core/catalogue.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import {
  parseSubmissionMetadataJSON,
  validateSubmissionMetadata,
} from "./submission-metadata.mjs";
import { certificate, historicalCertificate } from "./certificate.mjs";
import {
  submissionId,
  submissionDirectories,
  validateSubmissionDirectory,
} from "./submission-paths.mjs";

export function maintenancePaths(files) {
  return files
    .flatMap((f) => [
      f.filename,
      ...(f.previous_filename ? [f.previous_filename] : []),
    ])
    .some(
      (p) =>
        /^(submissions|proofs|public\/proofs|catalogue|public\/certificates|registry\/records)\//.test(
          p,
        ) ||
        ["public/catalogue.json", "public/registry.json"].includes(p) ||
        (/\.lean$/i.test(p) && !/^(verifier|core|tests)\//.test(p)),
    );
}

export function maintenancePlan({
  files,
  read,
  list,
  admittedCatalogue,
  readAdmittedCertificate,
  submittedAt,
  sameContents = (basePath, headPath) => {
    const before = read("base", basePath);
    return before !== null && before === read("head", headPath);
  },
}) {
  if (
    files.some(
      (file) =>
        /^(proofs|public\/proofs)\//.test(file.filename) &&
        file.status !== "removed",
    )
  )
    throw Error(
      "Submission source and metadata belong in submissions/YYYY-MM-DD-<slug>/",
    );
  if (
    files.some(
      (file) =>
        (["catalogue/results.json", "public/catalogue.json"].includes(
          file.filename,
        ) ||
          file.filename.startsWith("public/certificates/")) &&
        file.status !== "removed",
    )
  )
    throw Error(
      "Catalogue and certificate JSON are generated output; edit submissions/YYYY-MM-DD-<slug>/metadata.json instead",
    );
  const archived = admittedCatalogue
    ? catalogueProofRecords(admittedCatalogue)
    : [];
  const archiveIds = new Set(archived.map(proofRevision));
  const paths = Object.fromEntries(
    ["base", "head"].map((side) => [side, new Set(list(side, "submissions/"))]),
  );
  const directories = Object.fromEntries(
    ["base", "head"].map((side) => [
      side,
      submissionDirectories(
        new Set([...paths[side]].map((path) => path.split("/")[1])),
      ),
    ]),
  );
  const metadataPath = (side, id) => {
    const directory = directories[side].get(id);
    return directory ? `submissions/${directory}/metadata.json` : null;
  };
  const metadata = (side, id) => {
    const path = metadataPath(side, id);
    const bytes = path ? read(side, path) : null;
    return bytes ? parseSubmissionMetadataJSON(bytes) : null;
  };
  const metadataCatalogue = (side) => {
    const records = [],
      historical_records = [];
    for (const path of [...paths[side]].filter((path) =>
      /^submissions\/[^/]+\/metadata\.json$/.test(path),
    )) {
      const input = parseSubmissionMetadataJSON(read(side, path));
      const id = submissionId(path.split("/")[1]);
      if (!input.id) {
        validateSubmissionMetadata(input);
        const admitted =
          admittedCatalogue &&
          catalogueProofRecords(admittedCatalogue).find(
            (r) => proofRevision(r) === id,
          );
        if (!admitted)
          throw Error(
            `Cannot determine the exact bound for ${id}; provide a QRH result declaration`,
          );
        records.push(admitted);
        continue;
      }
      const admitted = archived.find(
        (record) => proofRevision(record) === input.id,
      );
      if (admitted && !metadata("base", id)?.id)
        throw Error(`Metadata duplicates an admitted proof: ${input.id}`);
      const {
        historical,
        dependencies,
        verification,
        agent_traces,
        ...record
      } = input;
      if (id !== proofRevision(record))
        throw Error("Proof metadata path differs from its revision");
      (historical === true ? historical_records : records).push(record);
    }
    return { schema_version: 1, records, historical_records };
  };
  const base = metadataCatalogue("base");
  const head = validateCatalogue(metadataCatalogue("head"));
  const ids = new Set(directories.head.keys());
  for (const [id, directory] of directories.head) {
    for (const file of ["metadata.json", "src/Candidate/Main.lean"])
      if (
        !paths.head.has(`submissions/${directory}/${file}`) ||
        read("head", `submissions/${directory}/${file}`) === null
      )
        throw Error(`Submission ${id} requires ${file}`);
    if (directory !== directories.base.get(id)) {
      const originalDate =
        /^\d{4}-\d{2}-\d{2}(?=-)/.exec(directories.base.get(id) ?? "")?.[0] ||
        (
          metadata("base", id)?.submitted_at ||
          archived.find((record) => proofRevision(record) === id)?.submitted_at
        )?.slice(0, 10);
      if (originalDate && directory.slice(0, 10) !== originalDate)
        throw Error(
          `Submission directory must retain its original date ${originalDate}: ${directory}`,
        );
      validateSubmissionDirectory(directory, {
        submittedAt:
          metadata("base", id)?.submitted_at ||
          archived.find((record) => proofRevision(record) === id)
            ?.submitted_at ||
          /^\d{4}-\d{2}-\d{2}(?=-)/.exec(directories.base.get(id) ?? "")?.[0] ||
          (!directories.base.has(id) && !archiveIds.has(id)
            ? submittedAt || ""
            : undefined),
      });
    }
  }
  for (const record of catalogueProofRecords(head))
    if (!ids.has(proofRevision(record)))
      throw Error(`Missing Lean submission: ${proofRevision(record)}`);
  const old = new Map(
    catalogueProofRecords(base).map((r) => [proofRevision(r), r]),
  );
  const records = new Map(
    catalogueProofRecords(head).map((r) => [proofRevision(r), r]),
  );
  const required = new Map();
  const requireProof = (id) => {
    if (!/^[a-z][a-z0-9-]{2,63}$/.test(id))
      throw Error(`Invalid proof result ID: ${id}`);
    const record = records.get(id) || old.get(id);
    if (!record)
      throw Error(
        `Cannot determine the exact bound for ${id}; provide its proof metadata or a QRH result declaration`,
      );
    required.set(id, { result_id: id, theta_exact: boundLabel(record) });
  };
  const identity = (r) => [
    boundLabel(r),
    r.theta,
    r.bound_interval,
    r.status,
    r.repository?.toLowerCase(),
    r.source_commit,
    r.entrypoint,
    r.first_verified_at,
  ];
  for (const [id, record] of records) {
    if (
      !old.has(id) ||
      !isDeepStrictEqual(identity(old.get(id)), identity(record))
    )
      requireProof(id);
    if (record.status !== "framework-verified") continue;
    const name = `public/certificates/${id}.json`;
    if (record.certificate_url !== `certificates/${id}.json`)
      throw Error(`Missing verification record: ${id}`);
    const certificateData = (side) => {
      const input = metadata(side, id);
      if (input?.id && input.verification)
        return JSON.stringify(historicalCertificate(input));
      // Read earlier committed receipts when comparing a migration's base.
      return (
        read(side, name) ||
        (archiveIds.has(id) ? readAdmittedCertificate?.(id) : null)
      );
    };
    const c = certificate(JSON.parse(certificateData("head")));
    if (
      c.result_id !== id ||
      c.theta_exact !== boundLabel(record) ||
      c.verified_at !== record.first_verified_at ||
      (record.source_commit && c.source_commit !== record.source_commit) ||
      (record.repository &&
        c.source_repository.toLowerCase() !==
          record.repository.toLowerCase()) ||
      !isDeepStrictEqual(c.bound_interval, record.bound_interval)
    )
      throw Error(`Verification record differs from catalogue: ${id}`);
    const previous = certificateData("base");
    if (previous) {
      const normalize = (value) => ({
        ...value,
        source_repository: value.source_repository.toLowerCase(),
      });
      if (
        !isDeepStrictEqual(
          normalize(certificate(JSON.parse(previous))),
          normalize(c),
        )
      )
        requireProof(id);
    }
  }
  const sourceIds = new Set();
  for (const f of files) {
    for (const path of [
      f.filename,
      ...(f.previous_filename ? [f.previous_filename] : []),
    ]) {
      const m = /^submissions\/([^/]+)\/(.+)$/.exec(path);
      if (m && m[2] !== "metadata.json") {
        const id = submissionId(m[1]);
        const before = directories.base.get(id);
        const after = directories.head.get(id);
        if (
          !before ||
          !after ||
          !sameContents(
            `submissions/${before}/${m[2]}`,
            `submissions/${after}/${m[2]}`,
          )
        )
          sourceIds.add(id);
      } else if (
        /\.lean$/i.test(path) &&
        !/^(verifier|core|tests)\//.test(path) &&
        f.status !== "removed" &&
        path === f.filename
      )
        throw Error(
          `Place maintained proof source in submissions/YYYY-MM-DD-<slug>/src: ${path}`,
        );
    }
  }
  const graph = new Map();
  for (const id of ids) {
    const deps = submissionDependencies(metadata("head", id));
    for (const dep of deps)
      if (!ids.has(dep))
        throw Error(`Missing submission dependency: ${id} -> ${dep}`);
    graph.set(id, deps);
    const before = metadata("base", id);
    if (!before || !isDeepStrictEqual(submissionDependencies(before), deps))
      sourceIds.add(id);
  }
  const visited = new Set(),
    active = new Set();
  function visit(id) {
    if (active.has(id)) throw Error(`Cyclic submission dependencies: ${id}`);
    if (visited.has(id)) return;
    active.add(id);
    for (const dep of graph.get(id)) visit(dep);
    active.delete(id);
    visited.add(id);
  }
  for (const id of ids) visit(id);
  for (const id of affectedSubmissions(sourceIds, graph)) {
    if (directories.head.has(id)) requireProof(id);
  }
  if (
    files.some(
      (f) => f.filename === "public/catalogue.json" && f.status !== "removed",
    )
  ) {
    const published = JSON.parse(read("head", "public/catalogue.json"));
    if (!isDeepStrictEqual(published, head))
      throw Error("Published catalogue differs from catalogue/results.json");
  }
  if (required.size > 256)
    throw Error("A PR can validate at most 256 affected proofs");
  return [...required.values()].sort((a, b) =>
    a.result_id.localeCompare(b.result_id),
  );
}

export async function maintenanceVerification(root, { pr, files, repository }) {
  if (!maintenancePaths(files)) return [];
  if (
    !/^[\w.-]+\/[\w.-]+$/.test(repository) ||
    ![pr.base.sha, pr.head.sha].every((s) => /^[a-f0-9]{40}$/.test(s))
  )
    throw Error("Invalid maintenance validation identity");
  const directory = mkdtempSync(join(tmpdir(), "qrh-maintenance-"));
  const git = (args) =>
    execFileSync("git", ["-c", "core.hooksPath=/dev/null", ...args], {
      cwd: directory,
      encoding: "utf8",
      timeout: 300000,
      maxBuffer: 32 * 1024 ** 2,
      env: {
        PATH: process.env.PATH,
        GIT_CONFIG_NOSYSTEM: "1",
        GIT_CONFIG_GLOBAL: "/dev/null",
        GIT_TERMINAL_PROMPT: "0",
        GIT_NO_REPLACE_OBJECTS: "1",
        GIT_ALLOW_PROTOCOL: "https",
      },
      stdio: ["ignore", "pipe", "pipe"],
    });
  const refs = { base: pr.base.sha, head: pr.head.sha };
  const trees = new Map();
  const tree = (ref) => {
    if (!trees.has(ref))
      trees.set(
        ref,
        new Map(
          git(["ls-tree", "-rz", refs[ref]])
            .split("\0")
            .filter(Boolean)
            .map((entry) => {
              const separator = entry.indexOf("\t");
              return [entry.slice(separator + 1), entry.slice(0, separator)];
            }),
        ),
      );
    return trees.get(ref);
  };
  const list = (ref, path) =>
    [...tree(ref).keys()].filter((entry) => entry.startsWith(path));
  const regularBlob = (ref, path) => {
    const entry = tree(ref).get(path);
    if (!entry) return null;
    if (!/^100644 blob [a-f0-9]{40}$/.test(entry))
      throw Error(`Expected a regular data file: ${path}`);
    return entry;
  };
  const read = (ref, path) => {
    const entry = regularBlob(ref, path);
    if (!entry) return null;
    return git(["show", `${refs[ref]}:${path}`]);
  };
  try {
    git(["init", "--bare", "--template="]);
    git(["remote", "add", "origin", `https://github.com/${repository}.git`]);
    git(["config", "remote.origin.promisor", "true"]);
    git(["config", "remote.origin.partialclonefilter", "blob:none"]);
    git([
      "fetch",
      "--no-tags",
      "--filter=blob:none",
      "--depth=1",
      "origin",
      refs.base,
      refs.head,
    ]);
    const cataloguePath = join(root, "catalogue/results.json");
    return maintenancePlan({
      files,
      read,
      list,
      submittedAt: pr.created_at,
      sameContents: (basePath, headPath) => {
        const before = regularBlob("base", basePath);
        return before !== null && before === regularBlob("head", headPath);
      },
      admittedCatalogue: existsSync(cataloguePath)
        ? JSON.parse(readFileSync(cataloguePath, "utf8"))
        : undefined,
      readAdmittedCertificate: (id) => {
        const path = join(root, `public/certificates/${id}.json`);
        return existsSync(path) ? readFileSync(path, "utf8") : null;
      },
    });
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}
