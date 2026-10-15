import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { record as catalogueRecord } from "./fixtures/catalogue.mjs";
const repository = "GTimG/QuasiRiemannTracker",
  head = "a".repeat(40);
const entrypoint = new URL("../verifier/actions/finalize.mjs", import.meta.url)
  .href;
function fixture() {
  const expected = {
    repository,
    number: 15,
    head_sha: head,
    result_id: "candidate-proof",
    theta_exact: "1/1",
  };
  const pr = {
    number: 15,
    state: "open",
    title: "A verified candidate bound",
    created_at: "2026-10-12T00:00:00Z",
    user: { login: "contributor" },
    head: { sha: head },
    base: { sha: "b".repeat(40), ref: "main", repo: { full_name: repository } },
    body: 'QRH-Result: candidate-proof\nQRH-Bound: 1/1\nQRH-Decimal: 1.0\n\n```qrh-metadata\n{"title":"A candidate bound","authors":[{"name":"Contributor"}],"description":"An independently verified proof."}\n```',
    changed_files: 1,
  };
  return {
    catalogue: {
      schema_version: 1,
      records: [
        catalogueRecord({
          id: "previous-bound",
          timeline_at: "2026-10-12T00:00:00Z",
          first_verified_at: "2026-10-12T01:00:00Z",
          certificate_url: "certificates/previous-bound.json",
        }),
      ],
    },
    context: {
      expected,
      expectations: [expected],
      pr,
      repository,
      defaultBranch: "main",
      run_id: "123",
      run_attempt: "1",
      workflow_sha: "c".repeat(40),
      check_id: 456,
    },
    current: structuredClone(pr),
    attempt: {
      ...expected,
      status: "accepted",
      report: {
        status: "PASS",
        verified_at: "2026-10-13T00:00:00Z",
        reviewed_pr_head: head,
        source_repository: repository,
        result_id: expected.result_id,
        theta_exact: "1/1",
        judge_exit_code: 0,
        targets: ["QRH.canonical_bound"],
        kernels: ["Lean default", "nanoda", "con-ron"],
        allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
        sandbox_preflight: "PASS",
        candidate_mount_preflight: "PASS",
        challenge_exported_before_candidate_execution: true,
        receipt_outside_candidate: true,
      },
    },
  };
}
function run(t, data, env = {}) {
  const cwd = mkdtempSync(join(tmpdir(), "qrh-finalize-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  for (const dir of ["verification-context", "verification"])
    mkdirSync(join(cwd, dir));
  writeFileSync(
    join(cwd, "verification-context/context.json"),
    JSON.stringify(data.context),
  );
  if (data.attempt)
    writeFileSync(
      join(cwd, "verification/attempt.json"),
      JSON.stringify(data.attempt),
    );
  mkdirSync(join(cwd, "verification/run"));
  writeFileSync(
    join(cwd, "verification/run/result.json"),
    JSON.stringify(data.attempt?.report ?? {}),
  );
  if (data.context.expectations)
    for (const expected of data.context.expectations) {
      const directory = join(
        cwd,
        `verification-results/proof-verification-1-${expected.result_id}`,
      );
      mkdirSync(join(directory, "run"), { recursive: true });
      const attempt = data.attempts
        ? data.attempts[expected.result_id]
        : data.attempt;
      if (attempt) {
        writeFileSync(join(directory, "attempt.json"), JSON.stringify(attempt));
        writeFileSync(
          join(directory, "run/result.json"),
          JSON.stringify(attempt.report),
        );
        writeFileSync(
          join(directory, "worker-status.json"),
          JSON.stringify({
            result: data.completions?.[expected.result_id] || "success",
          }),
        );
      }
    }
  writeFileSync(
    join(cwd, "verification-context/catalogue.json"),
    JSON.stringify(data.catalogue),
  );
  const script = `
 const requests=[];let prReads=0;globalThis.fetch=async(url,options={})=>{
 const request={url:String(url),method:options.method??"GET",body:options.body?JSON.parse(options.body):undefined};requests.push(request);
 if(request.method==="GET" && request.url==="https://api.github.com/repos/${repository}/pulls/15")return {ok:true,status:200,json:async()=>JSON.parse(prReads++ && process.env.FINAL_PR ? process.env.FINAL_PR : process.env.CURRENT_PR)};
 if(request.method==="GET" && request.url.includes("/git/blobs/")) {
 const body=JSON.parse(process.env.CURRENT_PR).body;
 const match=/\x60\x60\x60qrh-metadata\\n([\\s\\S]*?)\\n\x60\x60\x60/.exec(body);
 return {ok:true,status:200,json:async()=> match ? {type:"file",encoding:"base64",size:match[1].length,content:Buffer.from(match[1]).toString("base64")} : {}};
 }
 if(request.method==="GET" && request.url.includes("/git/trees/")){
 const key=request.url.split("/").at(-1);
 const item=(path,sha,type="tree",mode="040000")=>({path,sha:sha.repeat(40),type,mode});
 const tree=key==="${head}"?[item("submissions","d")]:key==="d".repeat(40)?[item("candidate-proof","e")]:key==="e".repeat(40)?[item("src","f"),item("metadata.json","1","blob","100644")]:key==="f".repeat(40)?[item("Candidate","2")]:[item("Main.lean","3","blob","100644")];
 return {ok:true,status:200,json:async()=>({tree})};}
 if(request.method==="GET" && request.url.endsWith("/git/ref/heads/admission-records"))return {ok:false,status:404};
 if(request.method==="POST" && /\\/git\\/(blobs|trees|commits|refs)$/.test(request.url))return process.env.ARCHIVE_FAILURE ? {ok:false,status:403} : {ok:true,status:201,json:async()=>({sha:"${"9".repeat(40)}"})};
 if(request.method==="PATCH" && request.url==="https://api.github.com/repos/${repository}/check-runs/456")return {ok:true,status:200};
 throw Error("Unexpected request");};
 let error;try{await import(${JSON.stringify(entrypoint)});}catch(e){error=e.message;process.exitCode=1;}
 console.log("RESULT="+JSON.stringify({requests,error}));`;
  const child = spawnSync(
    process.execPath,
    ["--input-type=module", "--eval", script],
    {
      cwd,
      encoding: "utf8",
      timeout: 10000,
      env: {
        GITHUB_REPOSITORY: repository,
        GITHUB_RUN_ID: "123",
        GITHUB_RUN_ATTEMPT: "1",
        GITHUB_WORKFLOW_SHA: "c".repeat(40),
        GITHUB_REF: "refs/heads/main",
        QRH_VERIFICATION_RESULT: "success",
        GITHUB_TOKEN: "test-token",
        CURRENT_PR: JSON.stringify(data.current),
        ...env,
      },
    },
  );
  assert.ifError(child.error);
  const line = child.stdout.split("\n").find((l) => l.startsWith("RESULT="));
  assert.ok(line, child.stderr);
  return { ...JSON.parse(line.slice(7)), status: child.status };
}
test("publisher accepts current-run proof without reading local receipts", (t) => {
  const result = run(t, fixture());
  assert.equal(result.status, 0);
  const published = result.requests.at(-1).body;
  assert.equal(published.conclusion, "success");
  assert.match(
    published.output.summary,
    /Proof verification accepts candidate-proof at 1\/1/,
  );
  const archived = result.requests.findIndex((r) =>
    r.url.endsWith("/git/refs"),
  );
  assert.ok(archived > 0, "archive is durable before publishing success");
  assert.ok(archived < result.requests.length - 1);
});
test("archive failure prevents a successful admission check", (t) => {
  const result = run(t, fixture(), { ARCHIVE_FAILURE: "1" });
  assert.equal(result.status, 1);
  assert.equal(result.requests.at(-1).body.conclusion, "failure");
  assert.match(
    result.requests.at(-1).body.output.summary,
    /archive request failed: HTTP 403/,
  );
});
test("new-bound admission requires publication metadata before archival", (t) => {
  const data = fixture();
  data.context.pr.body = data.current.body = data.current.body.split("\n\n")[0];
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.requests.at(-1).body.conclusion, "failure");
  assert.match(result.requests.at(-1).body.output.summary, /metadata/i);
  assert.ok(
    result.requests.every(
      (r) => !(r.method === "POST" && r.url.includes("/git/")),
    ),
  );
});

test("an unpublished predecessor fails admission before writing an archive", (t) => {
  const data = fixture();
  data.context.pr.body = data.current.body = data.current.body.replace(
    '"description":"An independently verified proof."',
    '"description":"An independently verified proof.","builds_on":["missing-proof"]',
  );
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.requests.at(-1).body.conclusion, "failure");
  assert.match(
    result.requests.at(-1).body.output.summary,
    /Unknown or later catalogue predecessor/,
  );
  assert.ok(
    result.requests.every(
      (r) => !(r.method === "POST" && r.url.includes("/git/")),
    ),
  );
});

test("a previously published result ID cannot receive new-bound admission", (t) => {
  const data = fixture();
  data.catalogue.records[0].id = "candidate-proof";
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.requests.at(-1).body.conclusion, "failure");
  assert.match(
    result.requests.at(-1).body.output.summary,
    /Result ID already published/,
  );
  assert.ok(
    result.requests.every(
      (r) => !(r.method === "POST" && r.url.includes("/git/")),
    ),
  );
});
test("a PR changed during archival cannot receive admission success", (t) => {
  const data = fixture();
  const changed = structuredClone(data.current);
  changed.head.sha = "f".repeat(40);
  const result = run(t, data, { FINAL_PR: JSON.stringify(changed) });
  assert.equal(result.status, 1);
  assert.equal(result.requests.at(-1).body.conclusion, "failure");
  assert.match(
    result.requests.at(-1).body.output.summary,
    /changed while archiving/,
  );
});
for (const field of ["head", "body", "base"])
  test(`publisher rejects stale ${field}`, (t) => {
    const data = fixture();
    if (field === "body") data.current.body += "\nchanged";
    else data.current[field].sha = "d".repeat(40);
    const result = run(t, data);
    assert.equal(result.status, 1);
    assert.equal(result.requests.at(-1).body.conclusion, "failure");
    assert.match(
      result.requests.at(-1).body.output.summary,
      /changed during verification/,
    );
  });
for (const field of ["run_id", "run_attempt", "workflow_sha"])
  test(`publisher refuses artifacts from another ${field}`, (t) => {
    const data = fixture();
    data.context[field] = "other";
    const result = run(t, data);
    assert.equal(result.status, 1);
    assert.equal(result.requests.length, 0);
    assert.match(result.error, /protected workflow run/);
  });
test("publisher fails a missing result artifact", (t) => {
  const data = fixture();
  delete data.attempt;
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(result.requests.at(-1).body.output.summary, /report is missing/);
});
test("publisher checks decimal accuracy after successful proof verification", (t) => {
  const data = fixture();
  data.context.pr.body = data.current.body = data.current.body.replace(
    "1.0",
    "1.1",
  );
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(result.requests.at(-1).body.output.summary, /decimal|Decimal/);
});

function batch() {
  const data = fixture();
  data.context.pr.body = data.current.body =
    "Maintenance of two proofs and the website.";
  data.context.expectations = [
    data.context.expected,
    { ...data.context.expected, result_id: "second-proof", theta_exact: "7/8" },
  ];
  const second = structuredClone(data.attempt);
  Object.assign(second, { result_id: "second-proof", theta_exact: "7/8" });
  Object.assign(second.report, {
    result_id: "second-proof",
    theta_exact: "7/8",
  });
  data.attempts = { "candidate-proof": data.attempt, "second-proof": second };
  return data;
}
test("maintenance publisher requires every affected proof and no declaration", (t) => {
  const result = run(t, batch());
  assert.equal(result.status, 0);
  const output = result.requests.at(-1).body;
  assert.equal(output.conclusion, "success");
  assert.match(output.output.summary, /Maintenance validations passed/);
  assert.match(output.output.summary, /second-proof at 7\/8/);
});
test("maintenance fails for the forbidden axiom in the second proof", (t) => {
  const data = batch();
  data.attempts["second-proof"].status = "checking-failed";
  data.attempts["second-proof"].reason = "Forbidden axiom: sorryAx";
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(
    result.requests.at(-1).body.output.summary,
    /Forbidden axiom: sorryAx/,
  );
});
test("maintenance rejects a missing result among several proofs", (t) => {
  const data = batch();
  delete data.attempts["second-proof"];
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(result.requests.at(-1).body.output.summary, /report is missing/);
});
test("maintenance requires successful worker completion for each accepted report", (t) => {
  const data = batch();
  data.completions = { "second-proof": "failure" };
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(
    result.requests.at(-1).body.output.summary,
    /job did not complete successfully/,
  );
});
