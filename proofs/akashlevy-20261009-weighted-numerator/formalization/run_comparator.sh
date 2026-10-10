#!/usr/bin/env bash
# Comparator (github.com/leanprover/comparator d03acab1 with lean4export 076e8e57, Lean 4.34.1) on one
# of the three Mathlib-only challenges in ComparatorChallenges/, after ./setup.sh has built the proof.
#   COMPARATOR              path to the comparator binary
#   COMPARATOR_LEAN4EXPORT  path to lean4export
#   COMPARATOR_LANDRUN      landrun (Linux sandbox); elsewhere an unsandboxed stand-in
# Usage: ./run_comparator.sh Zeta|Dirichlet|Hecke
set -euo pipefail
cd "$(dirname "$0")"
exec lake env "${COMPARATOR:?set COMPARATOR}" "ComparatorChallenges/WeightedQRH${1:?Zeta|Dirichlet|Hecke}.json"
