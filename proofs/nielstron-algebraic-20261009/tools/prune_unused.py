#!/usr/bin/env python3
"""Remove unreferenced, unannotated helper lemmas; a Lean rebuild is mandatory.

This is deliberately conservative source analysis, not a substitute for Lean.
Names are compared by their last component across all local sources, so name
collisions retain extra declarations. Definitions, attributes, public targets,
and the independent target specifications are preserved.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from count_lean_tokens import metric_module

BASE = Path(__file__).resolve().parents[1]
metric = metric_module(BASE / "lean-lean")

PROTECTED_FILES = {
    "QRH/Nonvanishing.lean", "QRH/DirichletTargets.lean",
    "QRH/HeckeTargets.lean", "QRH/IndependentTargets.lean",
    "QRH/StatementParity.lean",
}
# Public reformulations may be unused internally; retain their API as well.
PUBLIC_FILES = PROTECTED_FILES | {"QRH/ZeroBounds.lean"}
DECL = re.compile(r"^(?:private )?(?:theorem|lemma) ([\w.']+)", re.MULTILINE)
WORD = re.compile(r"[\w']+")


def prune(root: Path, *, protected_files: set[str] = PUBLIC_FILES) -> dict:
    sources = {p: p.read_text() for p in sorted(root.rglob("*.lean"))
               if ".lake" not in p.parts and p.name != "lakefile.lean"}
    removed = []
    before = sum(metric.count_lean_tokens_in_source(s) for s in sources.values())
    round_number = 0
    while True:
        masked = {p: metric.remove_lean_comments(s, mask_strings=True)
                  for p, s in sources.items()}
        counts = Counter(word for s in masked.values() for word in WORD.findall(s))
        changes = []
        for path, source in sources.items():
            if path.relative_to(root).as_posix() in protected_files:
                continue
            clean = masked[path]
            boundaries = [(offset, kind) for offset, indent, kind
                          in metric._command_boundaries(clean) if indent == 0]
            edits = []
            for match in DECL.finditer(clean):
                name = match[1]
                if counts[name.rsplit(".", 1)[-1]] != 1:
                    continue
                start = match.start()
                previous = [(off, kind) for off, kind in boundaries if off < start]
                if previous and previous[-1][1] == "attribute":
                    continue
                if previous and previous[-1][1] in {"include", "omit", "set_option"}:
                    if clean[previous[-1][0]:start].rstrip().endswith(" in"):
                        continue
                next_command = next((off for off, _ in boundaries if off > start), len(source))
                end = start + len(clean[start:next_command].rstrip())
                # A doc comment directly before the removed lemma belongs to it.
                prefix = source[:start].rstrip()
                if prefix.endswith("-/"):
                    doc = prefix.rfind("/--")
                    if doc >= 0 and not metric.remove_lean_comments(prefix[doc:]).strip():
                        start = doc
                edits.append((start, end, name))
            for start, end, name in reversed(edits):
                changes.append({
                    "file": path.relative_to(root).as_posix(), "declaration": name,
                    "round": round_number,
                    "tokens": metric.count_lean_tokens_in_source(source[start:end]),
                })
                source = source[:start] + source[end:]
            sources[path] = source
        if not changes:
            break
        removed.extend(changes)
        round_number += 1
    changed = 0
    for path, source in sources.items():
        if path.read_text() != source:
            path.write_text(source)
            changed += 1
    after = sum(metric.count_lean_tokens_in_source(s) for s in sources.values())
    return {"before_tokens": before, "after_tokens": after,
            "saved_tokens": before - after, "changed_files": changed,
            "removed": removed, "validation": "requires full Lean rebuild"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    report = prune(args.root.resolve())
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "removed"}))


if __name__ == "__main__":
    main()
