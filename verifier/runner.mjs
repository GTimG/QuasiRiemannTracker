import { spawn, spawnSync } from "node:child_process";
import {
  chmodSync,
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  readFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { randomUUID } from "node:crypto";
import { submission } from "./manifest.mjs";
import { challenge, solutionWrapper, comparatorConfig } from "./challenge.mjs";
import { sha256, PIN_DIGEST, iso } from "./common.mjs";
export const SECCOMP = fileURLToPath(
  new URL("../worker/seccomp.json", import.meta.url),
);
export function workerArgs(image, input, name) {
  if (!/^sha256:[a-f0-9]{64}$/.test(image))
    throw Error("Use a locally inspected immutable worker image ID");
  return [
    "run",
    "--rm",
    "--pull=never",
    "--name",
    name,
    "--network=none",
    "--read-only",
    "--user=65532:65532",
    "--cap-drop=ALL",
    "--security-opt=no-new-privileges",
    "--security-opt=seccomp=" + SECCOMP,
    "--pids-limit=256",
    "--memory=24g",
    "--memory-swap=24g",
    "--cpus=4",
    "--ulimit=nofile=1024:1024",
    "--ulimit=core=0:0",
    "--tmpfs=/tmp:rw,noexec,nosuid,nodev,size=1g,mode=1777",
    "--tmpfs=/work:rw,nosuid,nodev,size=20g,mode=1777",
    "--mount",
    `type=bind,source=${input},target=/input,readonly`,
    image,
  ];
}
export function preflight(image) {
  if (process.platform !== "linux")
    return (
      "Linux isolation required; host is " +
      process.platform +
      ". No proof checking was performed."
    );
  if (!/^sha256:[a-f0-9]{64}$/.test(image ?? ""))
    return "A maintainer-built, pinned worker image ID is required.";
  const r = spawnSync(
    "docker",
    ["info", "--format", "{{json .SecurityOptions}}"],
    { encoding: "utf8", timeout: 15000 },
  );
  if (r.status !== 0)
    return (
      "Rootless Docker unavailable: " +
      (r.stderr || r.error?.message || "unknown")
    );
  if (!r.stdout.includes("rootless"))
    return "Docker daemon must be rootless on a disposable Linux worker.";
  return null;
}
export function classify(exit, signal, timedOut, overflow) {
  if (timedOut) return "timed-out";
  if (overflow) return "resource-exhausted";
  if (signal || exit === null || exit === 125 || exit >= 128)
    return "checker-crash";
  if (exit === 0) return "accepted";
  return "checking-failed";
}
// Nonzero Comparator exit may mean elaboration, mathematical rejection, sandbox failure or kernel crash.
// Do not infer mathematical rejection from attacker-controlled output. Preserve diagnostic logs.
export async function check(dir, opts = {}) {
  const source = submission(dir),
    start = iso(),
    blocked = preflight(opts.image);
  const base = {
    kind: "qrh-check-attempt-v1",
    status: "infrastructure-blocked",
    started_at: start,
    completed_at: iso(),
    pin_digest: PIN_DIGEST,
    content_digest: source.content_digest,
    manifest_digest: source.manifest_digest,
    manifest: source.manifest,
    challenge_sha256: sha256(challenge(source.manifest)),
    source_commit: opts.sourceCommit ?? null,
    repository: opts.repository ?? null,
    pr: opts.pr ?? null,
    orchestrator_commit: opts.orchestratorCommit ?? null,
    worker_image: opts.image ?? null,
  };
  if (blocked)
    return {
      ...base,
      reason: blocked,
      log: blocked + "\n",
      results: {
        comparator: "not-run",
        nanoda: "not-run",
        isolation: "not-run",
      },
    };
  const input = mkdtempSync(path.join(tmpdir(), "qrh-input-")),
    name = "qrh-" + randomUUID();
  let text = "",
    timedOut = false,
    overflow = false,
    phase = "probe";
  try {
    chmodSync(input, 0o755);
    for (const f of source.files.filter((x) => x.path.startsWith("src/"))) {
      mkdirSync(path.dirname(path.join(input, f.path)), { recursive: true });
      writeFileSync(path.join(input, f.path), f.bytes, { mode: 0o444 });
    }
    writeFileSync(
      path.join(input, "Challenge.lean"),
      challenge(source.manifest),
      { mode: 0o444 },
    );
    writeFileSync(
      path.join(input, "Solution.lean"),
      solutionWrapper(source.manifest),
      { mode: 0o444 },
    );
    writeFileSync(
      path.join(input, "comparator.json"),
      JSON.stringify(comparatorConfig()),
      { mode: 0o444 },
    );
    const run = (extra) =>
      new Promise((resolve) => {
        const child = spawn(
          "docker",
          [...workerArgs(opts.image, input, name), ...extra],
          {
            env: {
              PATH: process.env.PATH,
              HOME: process.env.HOME,
              DOCKER_HOST: process.env.DOCKER_HOST ?? "",
              XDG_RUNTIME_DIR: process.env.XDG_RUNTIME_DIR ?? "",
            },
            stdio: ["ignore", "pipe", "pipe"],
          },
        );
        const kill = () => {
          spawnSync("docker", ["kill", name], {
            timeout: 15000,
            stdio: "ignore",
          });
          child.kill("SIGKILL");
        };
        const timer = setTimeout(() => {
          timedOut = true;
          kill();
        }, opts.timeoutMs ?? 3600000);
        const collect = (chunk) => {
          if (Buffer.byteLength(text) + chunk.length > 16 * 1024 * 1024) {
            overflow = true;
            kill();
          } else text += chunk.toString();
        };
        child.stdout.on("data", collect);
        child.stderr.on("data", collect);
        child.on("error", (e) => {
          text += e.message;
          clearTimeout(timer);
          resolve({ code: null, signal: "spawn-error" });
        });
        child.on("close", (code, signal) => {
          clearTimeout(timer);
          resolve({ code, signal });
        });
      });
    const probe = await run(["probe"]);
    if (probe.code !== 0)
      return {
        ...base,
        completed_at: iso(),
        reason: "Isolation preflight failed",
        log: text,
        results: {
          comparator: "not-run",
          nanoda: "not-run",
          isolation: "failed",
        },
      };
    phase = "check";
    const result = await run([]);
    const status = classify(result.code, result.signal, timedOut, overflow);
    const accepted = status === "accepted";
    return {
      ...base,
      status,
      completed_at: iso(),
      verified_at: accepted ? iso() : null,
      exit_code: result.code,
      signal: result.signal,
      log: text,
      log_sha256: sha256(text),
      results: {
        comparator: accepted ? "accepted" : status,
        nanoda: accepted ? "accepted" : "not-established",
        isolation: "passed",
      },
    };
  } finally {
    spawnSync("docker", ["rm", "-f", name], {
      timeout: 15000,
      stdio: "ignore",
    });
    rmSync(input, { recursive: true, force: true });
  }
}
