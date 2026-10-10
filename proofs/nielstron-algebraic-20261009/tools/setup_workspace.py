#!/usr/bin/env python3
"""Fetch the exact tracker and tokenizer Git objects needed for reproduction.

Pass --with-dependencies to also install the pinned Lean/source dependencies
and matching official mathlib cache. Existing modified checkouts are retained.
"""
from pathlib import Path
import argparse
import subprocess
import sys

from count_lean_tokens import TRACKER_COMMIT, TOKENIZER_COMMIT

ROOT = Path(__file__).resolve().parents[1]
REPOSITORIES = (
    ("tracker", "https://github.com/gtimg/QuasiRiemannTracker.git", TRACKER_COMMIT),
    ("lean-lean", "https://github.com/eth-sri/lean-lean.git", TOKENIZER_COMMIT),
)


def checkout(name, url, revision):
    destination = ROOT / name
    if not destination.exists():
        destination.mkdir()
        subprocess.run(["git", "init", str(destination)], check=True)
        subprocess.run(["git", "-C", str(destination), "remote", "add", "origin", url], check=True)
    if not (destination / ".git").is_dir():
        raise RuntimeError(f"Refusing to replace a non-repository directory: {destination}")

    def git(*args, check=True):
        return subprocess.run(["git", "-C", str(destination), *args], check=check,
                              text=True, capture_output=True)

    origin = git("remote", "get-url", "origin").stdout.strip()
    if origin.lower().removesuffix(".git") != url.lower().removesuffix(".git"):
        raise RuntimeError(f"Unexpected origin for {destination}: {origin}")
    head = git("rev-parse", "HEAD", check=False)
    if head.returncode or head.stdout.strip() != revision:
        if git("status", "--porcelain").stdout.strip():
            raise RuntimeError(f"Refusing to replace a modified checkout: {destination}")
        git("fetch", "--depth", "1", "origin", revision)
        git("checkout", "--detach", revision)
    assert git("rev-parse", "HEAD").stdout.strip() == revision
    print(f"{name}: {revision}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--with-dependencies", action="store_true")
    args = parser.parse_args()
    for name, url, revision in REPOSITORIES:
        checkout(name, url, revision)
    if args.with_dependencies:
        subprocess.run([sys.executable, str(ROOT / "compressed/scripts/setup_cached.py")], check=True)


if __name__ == "__main__":
    main()
