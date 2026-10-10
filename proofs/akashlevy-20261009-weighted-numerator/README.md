# Akash Levy: weighted numerator moments, θ = 10499/12000

Author: Akash Levy (GitHub [akashlevy](https://github.com/akashlevy)).
GPT-6 Astra (Ultra) was used to discover the proof and perform partial formalization; Opus 5.5 Ultracode was used to complete the formalization and submit the result.

This package proves in Lean 4, unconditionally, that none of the following
functions vanishes on the open half-plane `Re s > 10499/12000 = 0.874916666…`:

- Mathlib's Riemann zeta function `riemannZeta`;
- every Dirichlet L-function `DirichletCharacter.LFunction χ` of every positive
  modulus (Mathlib's definition), the pole of the trivial character at `s = 1`
  being excluded (`¬ (χ = 1 ∧ s = 1)`);
- every finite-order Hecke L-function of `Q(ζ₃)` in OpenAI's definition
  `OAI.SevenEighths.HeckeFamily.LFunction χ`, the pole being excluded
  (`s ≠ 1 ∨ χ.residue ≠ 1`).

It also proves `HeckeZeroSupremum.beta ≤ 10499/12000` (proved in Lean and
covered by the build and axiom checks, but outside the three Comparator
statements). The fraction is reduced.
The Hecke statements concern exactly the finite-order Hecke characters of
`Q(ζ₃)` in OpenAI's definition; they are not the generalized Riemann
hypothesis, and nothing is claimed for other fields. All half-planes are
strict. In the Comparator and tracker-template forms the zeta statement has no
hypothesis `s ≠ 1`, like the tracker's template for OpenAI's 7/8 result: it
holds at `s = 1` only because Mathlib assigns `riemannZeta 1` a nonzero value. The analytic statement
is `WeightedQRH.zeta_nonzero`.

**Catalogue status: framework-verified, proposed for maintainer review.** The
proposal rests on one author-side run of Comparator with the con-ron, NanoDa
and Lean kernels (check 1 below). That run used the official Lean v4.35.0-rc2
darwin_aarch64 binaries on macOS arm64 and ran **without a sandbox**
(`lake comparator --inadvisably-no-sandbox`), unlike the earlier sandboxed
Linux runs behind the tracker's other kernel dossiers. It is not a Palomar
registration, an editorial review or a signed tracker receipt, and it has not
been rerun independently. Maintainers may list the result as verification
pending until an independent sandboxed run. No external human peer review has
taken place.

## Lean statements

`formalization/WeightedQRH/Final.lean` (namespace `WeightedQRH`, with
`open OAI.SevenEighths`):

```lean
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (10499/12000:ℝ)
theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (10499/12000:ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0
theorem dirichlet_nonzero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (10499/12000:ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0
theorem zeta_nonzero (s : ℂ) (hs : (10499/12000:ℝ) < s.re) (h1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s ∧ riemannZeta s ≠ 0
```

Comparator form, `formalization/WeightedQRH/Statements.lean`, stated exactly
as the challenges in `formalization/ComparatorChallenges/`:

```lean
theorem OAI.riemannZeta_ne_zero_of_10499_12000_lt_re
    {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re) : riemannZeta s ≠ 0
theorem OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (10499 / 12000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0
theorem OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_10499_12000_lt_re
    (χ : Character) {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0
```

Tracker-template form: `evidence/kernels/src/Challenge.lean` is the tracker's
fixed three-target template `public/proofs/palomar-20261009/qrh/src/Challenge.lean`
(SHA-256 `eee59775c5f4f892199f7456f85f7664a14ef3010fc1b3df97ed2c0f8a1db4e6`)
with only the literal `874957019421 / 1000000000000` replaced by `10499 / 12000`
in all three statements (SHA-256
`4624fc67bbd5792408525558a48481a5cd3acd258c78caf1ec4d29528703c287`). The module
`Solution` (`evidence/kernels/src/Solution.lean`) imports
`WeightedQRH.Statements` and proves `QRHPalomar.allDirichlet`,
`QRHPalomar.zeta` and `QRHPalomar.allHecke` from the endpoints. The catalogue
entrypoint, like those of the earlier records, names the development's own
theorem: module `WeightedQRH.Statements`, declaration
`OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re`, which
`lake build` in `formalization/` builds and which `QRHPalomar.allDirichlet`
restates. `Solution` itself is not a module of the Lake workspace.

`formalization/WeightedQRH/FinalAxioms.lean` prints the axioms of ten
declarations, including the seven above; each depends only on `propext`,
`Classical.choice` and `Quot.sound`. `WeightedQRH.theta_lt_public`
(`Parameters.lean`) proves `theta < 874957019420098946128604623 / 10^27`, the
bound listed by the tracker at main `40844a7`; the exact difference is
`121058260296838385813869/3000000000000000000000000000` (about 4.0353 × 10⁻⁵).

## Method

The original cubic-theta probe of OpenAI's argument bounds its numerator
pointwise. This proof replaces that bound by a weighted fourth-moment estimate
for the actual smoothed numerator sum. Mellin inversion and the Hecke
functional equation reflect the physical numerator to a plain polynomial of
length at most `U/Y`, and the unused length carries selected prime factors in
the original fourth moment. A coefficient-norm argument controls the original
Euler correction, including its ramified error terms. The moment parameter
stays at the original `κ = 3/4`, with the geometry `ℓ = 167/1000`,
`b = 43/500`, `l_x = 747/2000`, `l_y = 919/2000`, `h = 1587/2000` and
`θ = 11/12 − ℓ/4 = 10499/12000`. The finite exponent comparisons are exact
rational certificates (`evidence/certificate/`). The written argument is
`manuscript/weighted_numerator_proof.tex` (it `\input`s
`weighted_numerator_lemma.tex`); the Lean proof does not depend on it.

## Pins

- Lean 4.34.1 (`leanprover/lean4:v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`), `formalization/lean-toolchain`.
- Original development: `github.com/akashlevy/math` at
  `c388e88e6519d139ad2ca5571ef0c7fbf0e245b5` (branch `qrh-23-24-pruned`; tag
  `qrh-weighted-10499-12000-base`),
  which is `github.com/openai/math` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
  with unused declarations pruned in place; its added 23/24 modules are not
  imported by this proof.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PrimeNumberTheoremAnd
  `c39a751132c88b6e8080b74c74023fd95b3d8be0` and rellich-kondrachov
  `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`, each with the fork's
  `lean/patches/<name>-lean4341.patch`; all packages in
  `formalization/lake-manifest.json`.
- Three-kernel judge: `lake comparator`, `leanchecker` (Lean default kernel),
  `nanoda_bin` and `con-ron` from the official Lean v4.35.0-rc2
  `lean-4.35.0-rc2-darwin_aarch64.tar.zst` (SHA-256
  `e721cf30671d3830fa6120c7b1a4e6b22624650ce1d618c0ca28a4889f5ef324`, equal to
  the asset digest GitHub publishes). Binary hashes are in
  `evidence/kernels/tool-pins.json` and `result.json` (`tool_sha256`).
- Exporter: lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, built with
  Lean 4.34.1.
- Default-kernel Comparator runs: Lean FRO Comparator
  `d03acab154d269c06e60e4de7e4cc85deebff94b` with lean4export `076e8e5`; its
  `lean-toolchain` was set to v4.34.1 (pinned v4.34.0) and Landrun was replaced
  by an unsandboxed stand-in.

## Checks and what each covered

All checks were run by the author on one macOS arm64 machine. Outside reports
cited below were read, not rerun.

1. **Comparator with con-ron, NanoDa and Lean's kernel** (`evidence/kernels/`).
   The driver `formalization/kernels/judge_three_kernels.py` (SHA-256
   `51495aba11b6addc5cfe4a05c647530e85ac36983e0c91bcfe12a41bdf8cd5c7`) was
   written for this run. It follows the earlier tracker dossiers
   (PalomarSubmission `d4e41c1` driving `lake comparator`) and re-implements
   their preflight controls, ill-typed export and export targets; it does not
   import Palomar's script.
   - Controls before judging, on the same toolchain
     (`control-results.json`, `controls/`; the control modules were compiled
     and exported with the judge release's own `lean` and `leanexport`, not
     with lean4export `076e8e5`): a matching pair exited 0 with all
     three kernels accepting (con-ron accepted 466 declarations); a mismatched
     statement exited 1 with "Challenge and solution theorem statement do not
     match"; an ill-typed proof (theorem value replaced by its type in the
     export) exited 1, rejected by con-ron, NanoDa and Lean's kernel.
   - The Challenge was compiled with Lean 4.34.1 against a pristine
     `openai/math` `fd4aeeb2e` checkout (the 306 OAI modules of the
     `Hecke/IdealBridge` closure built from source, 4402 Lake jobs;
     `pristine-workspace/`) and Mathlib `d13f23b7`; its search path held
     neither WeightedQRH nor the fork. `Hecke/Family.lean`,
     `Hecke/IdealBridge.lean`, Mathlib's `DirichletContinuation.lean` and
     `RiemannZeta.lean` match their pinned git blobs and the SHA-256 values
     used by the earlier tracker dossiers (`challenge-source-audit.json`). So
     Comparator compared the proof's definitions with unmodified upstream ones.
     The challenge's search path also held the original workspace's builds of
     PrimeNumberTheoremAnd `c39a7511` and rellich-kondrachov `70f85d4c` with
     the two Lean 4.34.1 compatibility patches applied, the same dependency
     builds the Solution used; no statement definition comes from them.
   - The Solution was compiled against the Lake build of check 2. Both were
     exported with lean4export `076e8e5`. `Challenge.export` (382347462 bytes,
     SHA-256 `f553d092b0690188ea806d9daadef9ec71179fd2d8e22a754dba6e40da9fbacb`)
     and `Solution.export` (1772535340 bytes, SHA-256
     `7ea84555c740c3840fd7f3a3d8cdf1ec987edb60d2825425511c52e6304358a3`) are
     not published; they were deleted after the run.
   - Binding to this snapshot: `result.json` does not hash the 228 module
     sources or their compiled objects; it records only the wrapper's SHA-256
     (`solution_sha256`). The link rests on the Solution's search path, which
     was the Lake build of the scratch workspace that is this
     `formalization/` directory. After the run, that workspace's
     `WeightedQRH/`, `ComparatorChallenges/`, `lakefile.toml`,
     `lean-toolchain`, `lake-manifest.json`, `setup.sh` and
     `run_comparator.sh` were re-checked to be byte-identical to this
     snapshot, no source or object there was newer than the build log, and
     its `math/` was a clean checkout of `c388e88e6`. That re-check is not
     recorded in the run's own files.
   - `lake comparator --challenge-from-export --solution-from-export` with
     `comparator.json` (the three theorem names, `definition_names` empty,
     permitted axioms `Classical.choice`, `Quot.sound`, `propext`, external
     kernels `nanoda_bin` and `con-ron --jobs=2`). The judge phase ran on
     2026-10-10 from 01:44:59 to 01:53:26 UTC and exited 0. `judge.log`
     reports "con-ron: accepted 123717 declarations (--verified)", "con-ron
     kernel accepts the solution", "nanoda kernel accepts the solution", "Lean
     default kernel accepts the solution" and "Your solution is okay!".
     `result.json`: status `PASS`, `verified_at_utc`
     `2026-10-10T01:53:26.235107+00:00`.
   - Caveats: no sandbox; `judge.log` begins with Comparator's "WARNING:
     Sandbox disabled, this run is not trustworthy." The binaries are the
     darwin_aarch64 ones, so their hashes differ from the Linux x86_64 pins of
     the earlier dossiers (PalomarSubmission `d4e41c1` on Linux x86_64 with
     bubblewrap). The challenge module is named `Challenge`, not a random
     `PalomarCanonical…` alias.
   - `tool-pins.json` and `challenge-source-audit.json` were not written by
     the driver and are not among the artifacts hashed by `result.json`. A
     separate, unpublished step wrote them about one minute after the judge
     finished (file times 01:54:20 and 01:54:21 UTC). Their values can be
     rechecked independently: the release digest against the asset digest
     GitHub publishes; the binary hashes against the unpacked release (they
     repeat `result.json`'s `tool_sha256`, which the driver recorded); and, for
     each protected definition file, `git -C <checkout> rev-parse
     <commit>:<path>` (the `git_blob`) and
     `git -C <checkout> show <commit>:<path> | shasum -a 256` (the `sha256`)
     in checkouts of openai/math `fd4aeeb2e` and Mathlib `d13f23b7`.
2. **Lake build from public sources** (`evidence/lake/lake-build.log`). The
   workspace was this `formalization/` directory with a fresh sparse clone of
   `akashlevy/math` at `c388e88e6` in `math/`. `lake build WeightedQRH
   ComparatorChallenges` reported "Build completed successfully (11847 jobs)"
   after 39 minutes; its log lists as built the 2670 modules of the original
   development in the proof's import closure, all 228 proof modules and the 3
   challenge modules. `lake build --no-build --rehash WeightedQRH
   ComparatorChallenges` then reported "All targets up-to-date (11847 jobs)"
   (`lake-no-build-rehash.log`). The `FinalAxioms.lean` output in the build
   log shows only the three standard axioms for all ten declarations. Caveat:
   `.lake/packages` was an existing checkout of the pinned dependencies with
   the two patches applied, so Mathlib and the other dependencies entered as
   prebuilt objects, and `.lake/build` was seeded with a copy of an earlier
   build of the original development. The fetch, patch and cache steps of
   `setup.sh` were therefore not exercised by this run; its patch step was
   tested separately on a fresh rellich-kondrachov clone at the pinned
   revision.
3. **Comparator with Lean's default kernel in the Lake workspace**
   (`evidence/lake/comparator-lake-WeightedQRH{Zeta,Dirichlet,Hecke}.log`).
   `run_comparator.sh Zeta|Dirichlet|Hecke` ran Comparator `d03acab1` (NanoDa
   disabled) with its real `lake build` step on the Mathlib-only challenges of
   `formalization/ComparatorChallenges/`. Each log ends with "Lean default
   kernel accepts the solution", "Your solution is okay!" and exit 0.
   `WeightedQRHDirichlet.lean` and `WeightedQRHHecke.lean` are OpenAI's
   upstream `DirichletSevenEighths` and `HeckeSevenEighths` challenges with only
   the theorem name and the constant changed.
4. **Earlier isolated rebuild** (`evidence/isolated-rebuild/`,
   `evidence/comparator/`), kept as an additional record.
   `verify_parallel.py` rebuilt the 228 proof modules and the 3 challenge
   modules with the live development directory removed from the search path,
   all with exit 0, on 2026-10-10 from 00:21:47 to 00:28:17 UTC
   (`final_rebuild_verification.json`); `WeightedQRH.FinalAxioms.log` shows the
   same three axioms. Comparator then ran on those objects with its
   `lake build` step replaced by a shim that only confirms the prebuilt
   objects exist: all three challenges were accepted by Lean's default kernel,
   and a negative control (zeta with 1/2 in place of 10499/12000) was rejected
   with "Challenge and solution theorem statement do not match"
   (`comparator-NegControl.log`; its challenge `WeightedQRHNegControl.lean` and
   configuration `WeightedQRHNegControl.json` are in `evidence/comparator/`).
   These scripts are kept as run. They assume the author's original directory
   layout (for example `verify_parallel.py` defaults to sibling
   `formalize_11_12/math` and `formalize_11_12/upstream` directories, and
   `run_comparator.sh` mentions a script there) and prebuilt objects at
   machine-specific locations, so they need `--source-checkout`, `OBJROOT`,
   `QRH_TOOLS` or edits before reuse.
5. **Source scan** (`evidence/source-scan.txt`): the 231 Lean files of
   `formalization/` contain none of `sorry`, `admit`, `axiom`, `unsafe`,
   `implemented_by`, `extern`, `native_decide`, `ofReduceBool`, `run_cmd`,
   `elab`, `macro`, `opaque` and the other listed keywords outside the three
   challenge statements (which are `sorry` by design); the only `set_option`s
   are `maxHeartbeats` and `maxRecDepth`.
6. **Exact exponent certificate** (`evidence/certificate/`): rational
   arithmetic only, with the original `κ = 3/4`.

## Comparison with public results

A dated, non-exhaustive public search (2026-10-10 00:16 UTC) found as the best
comparable unconditional claim the cubic root ≈ 0.87495701942009894613 of
Shunia with GPT-6 Astra and of Guo; Nielstron's Lean package for it is in the
open, unmerged tracker pull request #2. The tracker's listed best bound is
`874957019420098946128604623/10^27` (framework-verified). `10499/12000` is
lower by about 4.0353 × 10⁻⁵. No outside proof code was copied or reused.

## Reproduction

The certificate runs from the package root; the other commands run in
`formalization/` (the last two after `setup.sh`). The package stores every
file without the executable bit (the tracker's archive uses mode 0644), so
the shell scripts are run with `bash`. `setup.sh` needs git, curl and elan.
The placeholders are explained below the commands.

```sh
# package root: exact exponent certificate
python3 evidence/certificate/weighted_numerator_certificate.py --output <certificate.json>
# formalization/: Lake build from public sources
cd formalization && bash setup.sh
# formalization/: Comparator, default Lean kernel
export COMPARATOR=<comparator> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_LANDRUN=<landrun>
for c in Zeta Dirichlet Hecke; do bash run_comparator.sh $c; done
# formalization/: three-kernel check of the tracker template
python3 kernels/judge_three_kernels.py --solution-workspace . \
    --challenge-workspace <pristine> \
    --template <tracker>/public/proofs/palomar-20261009/qrh/src/Challenge.lean \
    --source-lean <lean-4.34.1> --judge-lean <lean-4.35.0-rc2> \
    --lean4export <lean4export> --out <fresh>
```

The certificate output should coincide with
`evidence/certificate/weighted_numerator_certificate.json`. Compiled objects
and proof exports are regenerated, not shipped.

**Fork commit.** `setup.sh` clones `akashlevy/math` and checks out
`c388e88e6`, which is reachable from the branch `qrh-23-24-pruned` and from the
annotated tag `qrh-weighted-10499-12000-base`, pushed to pin it (`git clone`
fetches tags, so the commit stays available if the branch is removed). If a
fresh clone does not contain that commit, fetch it by hash first (GitHub serves
a commit by hash only while some ref still reaches it); `setup.sh` skips the
clone when `math/.git` exists:

```sh
git clone --filter=blob:none --no-checkout https://github.com/akashlevy/math.git math
git -C math fetch origin c388e88e6519d139ad2ca5571ef0c7fbf0e245b5
git -C math sparse-checkout set --no-cone '/lean/OAI/NumberTheory/DirichletL/' '/lean/patches/' '/LICENSE'
git -C math checkout --detach c388e88e6519d139ad2ca5571ef0c7fbf0e245b5
```

**`<comparator>`, `<lean4export>`, `<landrun>`.** Build Comparator
`d03acab1` and its Lake dependency lean4export `076e8e5` after setting
Comparator's `lean-toolchain` to v4.34.1, to match the 4.34.1 objects (it
pins v4.34.0; its `lake-manifest.json` pins lean4export `076e8e5`):

```sh
git clone https://github.com/leanprover/comparator.git && cd comparator
git checkout --detach d03acab154d269c06e60e4de7e4cc85deebff94b
echo 'leanprover/lean4:v4.34.1' > lean-toolchain
lake build lean4export comparator
# <comparator>  = .lake/build/bin/comparator
# <lean4export> = .lake/packages/lean4export/.lake/build/bin/lean4export
```

`<landrun>` is Landrun on Linux. On macOS the recorded runs used the
following unsandboxed stand-in, which drops the sandbox arguments and runs the
command after `--` (Comparator's own `scripts/fake-landrun.sh` is a similar
shim); use it only for solutions you trust:

```sh
#!/usr/bin/env bash
while [[ $# -gt 0 && "$1" != "--" ]]; do shift; done
shift
exec "$@"
```

**`<pristine>` challenge workspace.** A Lake workspace with the
`lakefile.toml` and `lake-manifest.json` of
`evidence/kernels/pristine-workspace/`, the `lean-toolchain` of
`formalization/`, an unmodified `openai/math` checkout at `fd4aeeb2e` in
`math/` and the same two dependency patches. The patches are in that commit's
`lean/patches/`, blob-identical to the fork's. These commands mirror
`setup.sh`; they were not run as written, because the recorded workspace
(a sparse checkout of `lean/OAI/NumberTheory/DirichletL/`,
`lean/lean-toolchain` and `LICENSE`) shared the original workspace's already
patched dependency builds:

```sh
mkdir <pristine> && cd <pristine>
cp <package>/evidence/kernels/pristine-workspace/lakefile.toml .
cp <package>/evidence/kernels/pristine-workspace/lake-manifest.json .
cp <package>/formalization/lean-toolchain .
git clone --filter=blob:none --no-checkout https://github.com/openai/math.git math
git -C math sparse-checkout set --no-cone '/lean/OAI/NumberTheory/DirichletL/' '/lean/patches/' '/LICENSE'
git -C math checkout --detach fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
lake env true
for pkg in PrimeNumberTheoremAnd rellich-kondrachov; do
  git -C .lake/packages/$pkg apply "$PWD/math/lean/patches/$pkg-lean4341.patch"
done
lake exe cache get
lake build OAI.NumberTheory.DirichletL.Hecke.IdealBridge
```

**Other placeholders.** `<tracker>` is a tracker checkout; `<lean-4.34.1>` is
the Lean 4.34.1 toolchain directory; `<lean-4.35.0-rc2>` is the unpacked Lean
v4.35.0-rc2 release, whose `bin/` holds `nanoda_bin` and `con-ron`; `<fresh>`
must not exist.

**Sandbox.** The driver always passes `--inadvisably-no-sandbox` to
`lake comparator` and writes a fixed `sandbox` string into `result.json`
("bubblewrap needs Linux"). For a sandboxed run on Linux, remove that flag
from `judge()` in the driver; the recorded `sandbox` field, and the driver
hash in `tool-pins.json`, then no longer describe the run.

## Layout

- `formalization/`: Lake workspace (`lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `setup.sh`, `run_comparator.sh`), the 228 modules of
  `WeightedQRH/`, the three `ComparatorChallenges/` with their Comparator
  configurations, and `kernels/judge_three_kernels.py`.
- `manuscript/`: `weighted_numerator_proof.tex` and `weighted_numerator_lemma.tex`.
- `evidence/`: `kernels/` (three-kernel run), `lake/` (Lake build and
  default-kernel Comparator), `isolated-rebuild/` and `comparator/` (earlier
  route), `certificate/`, `source-scan.txt`.
- `LICENSE` (Apache-2.0), `NOTICE`, `UPSTREAM-NOTICE`, `third-party-notices/`,
  `PUBLICATION.md`, `publication-files.json`, `publication-transformations.json`.

Machine-specific path prefixes in logs and JSON reports are replaced by
`/work/qrh-proof/…`; `publication-transformations.json` records every changed
file with its original and published SHA-256, and `PUBLICATION.md` explains
the prefixes. Lean sources, the manuscript and license texts keep their bytes.
