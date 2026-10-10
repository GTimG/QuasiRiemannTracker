# Three-kernel verification

`result.json` records the completed check. `judge.log` contains the acceptance
lines for con-ron, NanoDa and Lean, followed by Comparator's success marker.
`judge-supervisor.json` records a zero exit, enforced resource limits and no
OOM event. `controls/` contains the successful proof, rejected changed
statement and rejected ill-typed-proof controls.

The Challenge and Solution wrappers are byte-identical to the executed run.
`../publication-map.json` maps publication copies to original evidence hashes.
Execution records replace private host paths and process IDs with symbolic
labels; the map records each transformation. Mathematical source is unchanged.

The two exports are large and are omitted with compiled caches. Their byte
lengths and SHA-256 hashes are in `export-pins.json`. `input-inventory.json`
lists the exact export targets and their order. Recompilation can produce
different artifact hashes; the frozen source inventory binds the input code.

## Reproduce

First build the bundled formalization using `../../REPRODUCE.md`. In a fresh
workspace, use these pinned tools and the hashes in `tool-pins.json`:

- [lean4export](https://github.com/leanprover/lean4export), commit
  `076e8e57707e813375e8f9da8bf989799ace9680`, built with Lean 4.34.1.
- The official [Linux Lean 4.35.0-rc2 bundle](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2),
  including Comparator, NanoDa and con-ron. The release archive hash is pinned.
- [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission),
  commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, for the compilation,
  export and control helpers used in this run.

Compile `Challenge.lean` and `Solution.lean` with Lean 4.34.1 in the
formalization's Lake environment. Write their `.olean` files into a fresh
directory and include that directory in `LEAN_PATH`. Invoke the compatible
exporter once per module:

```sh
lean4export MODULE -- TARGET...
```

Here `MODULE` is `Challenge` or `Solution`, and `TARGET...` is every entry of
`input-inventory.json`'s `export_targets` array, in order. Save each invocation's
stdout to its own export file. Use the same target list for both.

Copy `comparator.json` into a fresh working directory. Replace the two symbolic
external-kernel paths with absolute paths to `nanoda_bin` and `con-ron` in the
official 4.35.0-rc2 bundle, retaining `--jobs=2`. Put that bundle first on PATH
and run its Lake:

```sh
lake comparator --config comparator.json \
  --challenge-from-export Challenge.export \
  --solution-from-export Solution.export
```

Use a functioning Bubblewrap installation on Linux and retain Comparator's
kernel sandboxes. The recorded run used Bubblewrap 0.9.0, a 32 GiB memory
maximum, 1 GiB swap maximum, four CPUs, 512 tasks and a two-hour judge deadline.
The complete compile/export/judge sequence took about 14 minutes; the judge
peaked at about 7.8 GiB. No GPU was used.

## Execution record

`run-source/` preserves the actual launcher sources as historical evidence.
Its symbolic paths and original workspace layout need adaptation before reuse;
the commands above describe the portable mathematical check. The run used the
pinned Palomar helper for compilation, export and controls and official
Comparator with its built-in kernel sandboxes for judging. A cgroup supervisor
bounded the trusted parent process. The additional outer judge sandbox could
not run under this host's nested-Bubblewrap restrictions; no host security
policy was changed and no kernel sandbox was disabled.

Challenge has intentional specification `sorry` placeholders. Comparator
checks the Solution closures against the independently stated Challenge and
allows only `propext`, `Classical.choice` and `Quot.sound` in those proofs.
The seven exported roots and their full closures are the scope of this run.
These contributor-run results are not a signed registry admission receipt.
