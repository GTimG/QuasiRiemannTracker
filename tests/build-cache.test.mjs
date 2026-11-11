import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";

test("authenticated shared module cache rejects changed inputs and malformed archives", () => {
  const run = spawnSync("python3", ["tests/build-cache.py"], {
    encoding: "utf8",
  });
  assert.equal(run.status, 0, run.stdout + run.stderr);
});

test("proof workers upload diagnostics and then report failed verification", () => {
  const workflow = readFileSync(".github/workflows/pr-admission.yml", "utf8");
  const worker = workflow.split("  verify:\n")[1].split("  admission:\n")[0];
  assert.ok(
    worker.indexOf("Require successful worker verification") >
      worker.indexOf("actions/upload-artifact"),
  );
  assert.match(worker, /if: always\(\) && steps\.check\.outcome != 'success'/);
  assert.match(worker, /exit 1/);
});

test("scheduled cache builds cannot receive signing secrets or repository write access", () => {
  const workflow = readFileSync(".github/workflows/build-cache.yml", "utf8");
  const build = workflow.split("  build:\n")[1].split("  publish:\n")[0];
  const publisher = workflow.split("  publish:\n")[1];
  assert.match(workflow, /schedule:\n\s+- cron: "47 4 \* \* 1"/);
  assert.match(
    build,
    /github\.event_name == 'schedule' \|\| inputs\.rebuild_all == true/,
  );
  assert.match(build, /needs: signing-key/);
  assert.doesNotMatch(
    build,
    /secrets\.|contents: write|environment: build-cache/,
  );
  assert.match(build, /publish-cache\.py --prepare/);
  assert.match(publisher, /needs: build/);
  assert.match(publisher, /github\.ref == 'refs\/heads\/main'/);
  assert.match(publisher, /environment: build-cache/);
  assert.match(publisher, /secrets\.QRH_BUILD_CACHE_KEY/);
  assert.match(
    publisher,
    /name: cache-publication-\$\{\{ github\.run_attempt \}\}/,
  );
  assert.doesNotMatch(publisher, /run-id:|repository:|build\.py|lake |lean /);
});
