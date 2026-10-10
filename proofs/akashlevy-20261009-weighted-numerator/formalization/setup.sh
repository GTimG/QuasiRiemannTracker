#!/usr/bin/env bash
# Reproduce the theta = 10499/12000 Lean build from public sources.
#   1. fetch the original QRH development: github.com/akashlevy/math at the pinned commit
#      (openai/math fd4aeeb2e with unused declarations pruned), sparse checkout of lean/;
#   2. let Lake fetch the dependencies pinned in lake-manifest.json (Mathlib d13f23b7, ...);
#   3. apply the fork's Lean 4.34.1 compatibility patches to PrimeNumberTheoremAnd and
#      rellich-kondrachov (lean/patches/, the same patches openai/math applies);
#   4. download Mathlib's build cache and build the proof and the Comparator challenges.
# Requires git, curl and elan (Lean toolchain leanprover/lean4:v4.34.1 from lean-toolchain).
set -euo pipefail
cd "$(dirname "$0")"
FORK=https://github.com/akashlevy/math.git
COMMIT=c388e88e6519d139ad2ca5571ef0c7fbf0e245b5
if [[ ! -d math/.git ]]; then
  git clone --filter=blob:none --no-checkout "$FORK" math
  git -C math sparse-checkout set --no-cone '/lean/OAI/NumberTheory/DirichletL/' '/lean/patches/' '/LICENSE'
  git -C math checkout --detach "$COMMIT"
fi
[[ "$(git -C math rev-parse HEAD)" == "$COMMIT" ]] || { echo "math/ is not at $COMMIT" >&2; exit 1; }
lake env true   # resolves and clones the pinned dependencies into .lake/packages
for pkg in PrimeNumberTheoremAnd rellich-kondrachov; do
  patch="$PWD/math/lean/patches/$pkg-lean4341.patch"
  dir=".lake/packages/$pkg"
  if git -C "$dir" apply --reverse --check "$patch" 2>/dev/null; then
    echo "$pkg: compatibility patch already applied"
  else
    git -C "$dir" apply --check "$patch" && git -C "$dir" apply "$patch"
    git -C "$dir" apply --reverse --check "$patch"
    echo "$pkg: compatibility patch applied"
  fi
done
lake exe cache get
lake build WeightedQRH ComparatorChallenges
