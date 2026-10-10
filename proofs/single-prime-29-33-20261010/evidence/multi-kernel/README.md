# Local three-kernel verification

`result.json` records the completed check. `judge.log` contains the three kernel
acceptance lines and Comparator's final success marker. `judge-supervisor.json`
records zero exit, enforced cgroup limits, no OOM and no remaining job processes.
`controls/` contains the valid, wrong-statement and ill-typed-proof controls.

The mathematical Challenge and Solution wrappers are byte-identical to the run.
`publication-map.json` binds each published evidence file to its original hash.
Absolute host paths and cgroup identity are replaced with symbolic labels in
publication copies; `result.json` retains the ORIGINAL evidence hashes. Resolve
those through the map when checking a sanitized file. No proof source changed.

The two large proof exports are not included. `export-pins.json` records their
exact byte lengths and hashes. `input-inventory.json` records the original
source/artifact inventory and ordered export targets. Compiled artifacts are
also omitted. Source identity can be checked against the formalization and its
ordinary-Lean report; recompilation may produce different artifact hashes.

## Reproduce the mathematical check

First build the bundled formalization with its pinned Lean 4.34.1 dependencies
as described in the top-level proof README. Use a fresh workspace and the exact
tool versions in `tool-pins.json`:

- lean4export: https://github.com/leanprover/lean4export at
  `076e8e57707e813375e8f9da8bf989799ace9680`, built with Lean 4.34.1.
- Official Linux Lean bundle: https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2
  (release archive SHA-256 is recorded in the pins).
- Palomar helper source: https://github.com/PalomarRegistry/PalomarSubmission at
  `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.

Compile `Challenge.lean` and `Solution.lean` with the 4.34.1 compiler and the
formalization's Lake environment, placing their `.olean` files in a fresh
directory included on `LEAN_PATH`. Invoke the 4.34.1-compatible exporter once
per module as `lean4export MODULE -- TARGET...`, where TARGET is every entry
of `input-inventory.json`'s `export_targets` array in the recorded order. Save
stdout to a separate export file. Use the same input inventory for both exports.

Copy `comparator.used.json` to a fresh config and replace its two external
kernel paths with absolute paths to `nanoda_bin` and `con-ron` from the official
4.35.0-rc2 bundle, retaining `--jobs=2`. Run that bundle's Lake:

```sh
lake comparator --config comparator.json \
  --challenge-from-export Challenge.export \
  --solution-from-export Solution.export
```

Use an empty working directory and put the official checker bundle first on
PATH. On Linux, supply a functioning Bubblewrap installation; do not disable
Comparator's kernel sandboxes. The original run used `/usr/bin/bwrap` 0.9.0,
32 GiB memory max, 1 GiB swap max, four CPUs, 512 tasks, and a two-hour judge
deadline. It completed in about 12.5 minutes including export. Peak judge memory
was about 7.4 GiB. No GPU was involved.

## Executed launcher and limitations

`run-source/` preserves publication copies of the ACTUAL launcher sources used
for this run. They are historical execution evidence, not a turnkey installer:
their symbolic host paths and layout must be adapted before reuse. They call
the unchanged pinned Palomar helper for compilation, export and controls, and
the official Comparator with its own kernel sandboxes for judging. The extra
outer Palomar judge sandbox was not used because the host blocks nested
Bubblewrap. No host security policy was changed and no sandbox-disable flag
was used. There was no registry submission or signed acceptance receipt.

The run-source launcher predates a later local parent-liveness cleanup
improvement. During this run an exact-job guardian covered parent death and
the overall budget; it observed normal completion and took no action. That
host lifecycle mechanism is not part of the mathematical evidence.

Challenge intentionally contains specification `sorry` placeholders. The
Solution's proof closures are what the axiom check and three kernels validate.
Only the four selected closures are claimed independently checked, not every
unused local declaration or mathematical fidelity to the manuscript.
