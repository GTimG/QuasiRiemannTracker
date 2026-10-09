import { execFileSync } from "node:child_process";
import { immutableHistory } from "./history.mjs";
const rev = process.argv[2];
if (!/^[a-f0-9]{40}$/.test(rev ?? ""))
  throw Error("Supply the full trusted base commit");
function tree(ref) {
  const text = execFileSync("git", ["ls-tree", "-r", ref, "--", "registry/"], {
    encoding: "utf8",
  });
  return Object.fromEntries(
    text
      .trim()
      .split("\n")
      .filter(Boolean)
      .map((line) => {
        const [meta, file] = line.split("\t");
        return [file, meta.split(" ")[2]];
      }),
  );
}
immutableHistory(tree(rev), tree("HEAD"));
console.log("Historical registry is append-only.");
