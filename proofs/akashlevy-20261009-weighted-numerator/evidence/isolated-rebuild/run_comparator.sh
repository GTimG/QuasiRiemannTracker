#!/usr/bin/env bash
# Comparator check of a WeightedQRH challenge against objects built in isolation by
# verify_parallel.py (OBJROOT). Comparator's `lake build M` step is replaced by a shim that only
# confirms the prebuilt object exists; its export, statement comparison, axiom check and full
# kernel replay run unchanged. As in formalize_11_12/scripts/run-comparator-macos.sh, Landrun
# (Linux Landlock) is replaced by an unsandboxed shim.
# Challenge objects come from the sibling root OBJROOT/../challenges, which verify_parallel.py
# builds against Mathlib alone.
# Usage: OBJROOT=.verification/<run>/lib/lean bash run_comparator.sh Zeta|Dirichlet|Hecke
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
tools=${QRH_TOOLS:?set QRH_TOOLS to the tools directory holding comparator/ and landrun-shim}
objroot=$(cd "${OBJROOT:?set OBJROOT}" && pwd)
shim=$(mktemp -d)
cat > "$shim/lake" <<'EOS'
#!/usr/bin/env bash
[[ "${1:-}" == build ]] || { echo "lake shim: unsupported: $*" >&2; exit 2; }
f="$(echo "$2" | tr . /).olean"
IFS=: read -ra dirs <<< "$LEAN_PATH"
top="${2%%.*}"
# Lean resolves a module in the first root holding its top-level directory; do the same.
for d in "${dirs[@]}"; do
  if [[ -d "$d/$top" ]]; then
    [[ -f "$d/$f" ]] && { echo "lake shim: prebuilt $d/$f"; exit 0; }
    echo "lake shim: missing $d/$f" >&2; exit 1
  fi
done
echo "lake shim: no root holds $top" >&2; exit 1
EOS
chmod +x "$shim/lake"
external=$(python3 -c "import json,os;c=json.load(open('$root/lean_environment.json'));print(os.pathsep.join(p for p in c['LEAN_PATH'].split(os.pathsep) if os.path.realpath(p)!=os.path.realpath('$root')))")
challenges=$(cd "${CHALLENGES:-$objroot/../challenges}" && pwd)
export LEAN_PATH="$challenges:$objroot:$external"
export PATH="$shim:$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$PATH"
export COMPARATOR_LANDRUN="$tools/landrun-shim"
export COMPARATOR_LEAN4EXPORT="$tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
cd "$root"
printf 'Comparator starting: %s (objects %s)\n' "$1" "$objroot"
exec "$tools/comparator/.lake/build/bin/comparator" "$root/ComparatorChallenges/WeightedQRH$1.json"
