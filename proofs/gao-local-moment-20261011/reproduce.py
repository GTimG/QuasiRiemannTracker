#!/usr/bin/env python3
"""Fetch the pinned manuscript and verify the uploaded candidate bytes."""
import argparse, hashlib, json
from pathlib import Path
from urllib.request import Request, urlopen
ROOT = Path(__file__).resolve().parent
PAPER = "build/tracker_weighted_numerator_2026-10-10/latest-cycle25/paper.tex"
URL = "https://raw.githubusercontent.com/HaileyStorm/QuasiRiemannTracker/58344dfdbe756cf2f743da1908ffe0582418cf5b/public/proofs/cycle25-quartic-20261010/paper.tex"
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-pinned-paper", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((ROOT/"SHA256SUMS.json").read_text())
    for rel, digest in manifest.items():
        target = ROOT/rel
        assert target.resolve().is_relative_to(ROOT), rel
        assert hashlib.sha256(target.read_bytes()).hexdigest() == digest, rel
    audit = json.loads((ROOT/"research/numerics/results/local_physical_moment_audit.json").read_text())
    digest = audit["input_sha256"][PAPER]
    target = ROOT/"research"/PAPER
    if args.fetch_pinned_paper:
        with urlopen(Request(URL, headers={"User-Agent":"local-moment-candidate-replay"}), timeout=30) as r:
            payload = r.read(4*1024*1024+1)
        assert len(payload)<=4*1024*1024
        assert hashlib.sha256(payload).hexdigest() == digest, "Pinned paper digest mismatch"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
    assert target.is_file(), "Use --fetch-pinned-paper to obtain the exact referenced input"
    assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
    print("PASS: uploaded bytes and pinned manuscript; no kernel verification performed")
if __name__ == "__main__": main()
