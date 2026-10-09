import { readFileSync, writeFileSync } from "node:fs";
const input = process.argv[2] || "";
const repository = input
  .replace(/^https:\/\/github.com\//, "")
  .replace(/\.git$/, "")
  .replace(/\/$/, "");
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repository))
  throw Error(
    "Usage: npm run configure-repository -- https://github.com/OWNER/REPO",
  );
const config = JSON.parse(readFileSync("site.config.json", "utf8"));
writeFileSync(
  "site.config.json",
  JSON.stringify({ ...config, repository }, null, 2) + "\n",
);
console.log(
  `Prepared links for https://github.com/${repository}. No remote change or publication performed.`,
);
