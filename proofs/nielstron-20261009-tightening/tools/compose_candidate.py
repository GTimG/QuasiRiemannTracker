#!/usr/bin/env python3
"""Recreate the QRH compression candidate from a pinned, untouched baseline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

from count_lean_tokens import TRACKER_COMMIT, TRACKER_PREFIX, metric_module, baseline_sources, git
from prune_unused import prune, PROTECTED_FILES

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "combined-preview")
    parser.add_argument("--report", type=Path, default=ROOT / "combined-preview-report.json")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT / "tracker" or ROOT / "tracker" in output.parents:
        raise ValueError("The original tracker checkout must remain untouched")
    metric = metric_module(ROOT / "lean-lean")
    sources = baseline_sources(ROOT / "tracker", metric)
    for name in ("lakefile.lean", "lean-toolchain", "lake-manifest.json"):
        sources[name] = git(ROOT / "tracker", "show", f"{TRACKER_COMMIT}:{TRACKER_PREFIX}/{name}")
    for name, data in sources.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    overlays = []
    manual_edits = {}
    for metadata in sorted((ROOT / "manual").glob("*-compression.json")):
        records = json.loads(metadata.read_text())
        name = Path(records["file"]).relative_to("manual").as_posix()
        manual_edits[name] = (metadata, records)
    for directory in (ROOT / "candidates", ROOT / "manual"):
        if not (directory / "QRH").is_dir():
            continue
        for path in sorted((directory / "QRH").rglob("*.lean")):
            name = path.relative_to(directory).as_posix()
            if name in PROTECTED_FILES:
                raise ValueError(f"Refusing to replace protected source: {name}")
            if directory.name == "manual" and name in manual_edits:
                metadata, edits = manual_edits[name]
                text = (output / name).read_text()
                for edit in edits["changes"]:
                    short_name = edit["theorem"].rsplit(".", 1)[-1]
                    clean = metric.remove_lean_comments(text, mask_strings=True)
                    matches = list(re.finditer(r"^(?:theorem|lemma) " + re.escape(short_name) + r"\b", clean, re.M))
                    if len(matches) != 1:
                        raise ValueError(f"Missing/ambiguous manual theorem: {short_name}")
                    start = matches[0].start()
                    stop = next((offset for offset, indent, _ in metric._command_boundaries(clean)
                                 if offset > start and indent == 0), len(text))
                    end = start + len(clean[start:stop].rstrip())
                    body = clean.index(":= by", start, end) + len(":= by")
                    text = text[:body] + "\n" + edit["new_proof_body"].rstrip() + text[end:]
                (output / name).write_text(text)
                overlays.append({"file": name, "from": str(metadata.relative_to(ROOT)),
                                 "method": "replace named proof bodies, retain factored signatures"})
                continue
            (output / name).write_bytes(path.read_bytes())
            overlays.append({"file": name, "from": str(path.relative_to(ROOT))})
    # Public presentation lemmas remain available even when the analytic proof
    # does not call them. Their entire source is included in the token metric.
    presentation_files = set()
    for path in sorted((ROOT / "interfaces" / "QRH").rglob("*.lean")):
        name = path.relative_to(ROOT / "interfaces").as_posix()
        if name in sources:
            raise ValueError(f"Presentation module would replace original source: {name}")
        destination = output / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(path.read_bytes())
        presentation_files.add(name)
        overlays.append({"file": name, "from": str(path.relative_to(ROOT)),
                         "method": "add public reformulations; count all source tokens"})
    report = prune(output, protected_files=PROTECTED_FILES | presentation_files)
    if presentation_files:
        entrypoint = output / "QRH.lean"
        imports = "".join(f"import {Path(name).with_suffix('').as_posix().replace('/', '.')}\n"
                          for name in sorted(presentation_files))
        entrypoint.write_text(imports + entrypoint.read_text())
    for name in PROTECTED_FILES:
        if (output / name).read_bytes() != sources[name]:
            raise ValueError(f"Protected source changed: {name}")
    report.update({
        "baseline_commit": TRACKER_COMMIT,
        "baseline_tokens": sum(metric.count_lean_tokens_in_source(data.decode())
                               for name, data in sources.items()
                               if name.endswith(".lean") and name != "lakefile.lean"),
        "overlays": overlays,
        "protected_files_unchanged": sorted(PROTECTED_FILES),
        "public_presentation_files": sorted(presentation_files),
        "candidate_files": {path.relative_to(output).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                            for path in sorted(output.rglob("*.lean")) if ".lake" not in path.parts},
    })
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("baseline_tokens", "before_tokens", "after_tokens", "saved_tokens", "changed_files")}))


if __name__ == "__main__":
    main()
