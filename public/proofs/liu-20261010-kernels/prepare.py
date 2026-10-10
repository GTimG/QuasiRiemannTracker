#!/usr/bin/env python3
"""Restore the published Liu package's import layout without editing proofs.

The source repositories are fetched separately and are not redistributed by
this script. All copied proof bytes are recorded in source-manifest.json.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

LIU = "7d10420de90efa2f082a06a342fc7accbd57ab37"
OAI = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--liu", type=Path, required=True)
    ap.add_argument("--openai", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    records = []

    def write(dest, raw, repo, commit, original):
        p = args.output / dest
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw)
        records.append(dict(path=str(dest), sha256=digest(raw),
                            repository=repo, commit=commit, source=original))

    # Read git objects, not potentially changed working-tree files.
    names = git(args.liu, "ls-tree", "-r", "--name-only", LIU).decode().splitlines()
    for name in names:
        if name.endswith(".lean") and name != "lakefile.lean":
            src = Path(name)
            if len(src.parts) == 1:
                dest = src if name == "RHZeroFreeExtension.lean" else Path("RHZeroFreeExtension") / src
            elif src.parts[0] in {"analytic_high", "analytic_high_v2"}:
                dest = Path("RHZeroFreeExtension/analytic_high") / src.name
            elif src.parts[0] == "moment_adapters":
                dest = Path("RHZeroFreeExtension") / src
            else:
                dest = src
            if (args.output / dest).exists():
                existing = next((r for r in records if r["path"] == str(dest)), None)
                if existing:
                    raise RuntimeError("Colliding layout destinations: " + str(dest))
            write(dest, git(args.liu, "show", f"{LIU}:{name}"), "Liu", LIU, name)
        elif name in {"lakefile.lean", "lake-manifest.json", "lean-toolchain", "verify.py"} or name.startswith("upstream/"):
            write(Path(name), git(args.liu, "show", f"{LIU}:{name}"), "Liu", LIU, name)

    closure = json.loads((args.output / "upstream/closure_manifest.json").read_text())
    assert closure["commit"] == OAI
    for module, rec in closure["modules"].items():
        src = "lean/" + str(Path(rec["path"]).relative_to("vendor"))
        raw = git(args.openai, "show", f"{OAI}:{src}")
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if digest(raw) != rec["sha256"] or blob != rec["git_blob"]:
            raise RuntimeError("Declared source mismatch: " + module)
        write(Path(rec["path"]), raw, "openai/math", OAI, src)
    write(Path("vendor/LICENSE"), git(args.openai, "show", f"{OAI}:LICENSE"), "openai/math", OAI, "LICENSE")

    result = {"liu_commit": LIU, "openai_commit": OAI,
              "proof_text_modified": False,
              "layout_restoration": {
                  "root proof modules except RHZeroFreeExtension.lean": "RHZeroFreeExtension/",
                  "analytic_high and analytic_high_v2": "RHZeroFreeExtension/analytic_high/",
                  "moment_adapters": "RHZeroFreeExtension/moment_adapters/",
                  "geometry and analytic_low": "unchanged"},
              "files": records}
    (args.output.parent / "source-manifest.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "files": len(records),
                      "vendor_modules": len(closure["modules"]),
                      "output": str(args.output)}, indent=2))

if __name__ == "__main__":
    main()
