import { readJSON } from "./common.mjs";
import { synchronizeSubmissions } from "./submission-status.mjs";

const event = readJSON(process.env.GITHUB_EVENT_PATH);
const repo = process.env.GITHUB_REPOSITORY;
if (event.repository.full_name !== repo) throw Error("Wrong event repository");
await synchronizeSubmissions({
  repo,
  defaultBranch: event.repository.default_branch,
  policy: readJSON("verifier/trust-policy.json"),
});
