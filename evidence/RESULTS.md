# Validation results — 2026-10-09

## Completed checks

- ProofCouncil exact `874957019421/1000000000000` proof: **PASS** on Linux verification worker at 13:00:36 UTC.
- Original OpenAI `7/8` proof: **PASS** on Linux verification worker at 13:06:32 UTC.
- Both runs used Palomar’s mechanical judge: Comparator checked statements, definitions and axioms, then con-ron, NanoDa and Lean accepted the exported proofs. All-Dirichlet, zeta and finite-order Eisenstein Hecke targets were included. Only `propext`, `Classical.choice` and `Quot.sound` were allowed. Positive, mismatched-statement and ill-typed-proof preflights passed.
- Reports, exact statements, configurations, pins and acceptance logs: [`../public/proofs/palomar-20261009/`](../public/proofs/palomar-20261009/). These are local checks, separate from Palomar registration and editorial review. The README there records compiler and submission-policy limitations.
- Latest Node arithmetic/security/workflow/history tests: **19 passed**.
- TypeScript check and Vite production build: **passed**, including hashes for all 8,351 original proof snapshot files and the new kernel-check evidence.
- Latest Chromium desktop and mobile browser tests: **10 passed**. Screenshots in `screenshots/` show the website with the lineage view removed. The admitted-registry status test uses an isolated browser response mock; it does not add records to the public registry.

## Earlier checks and the separate signed service

The retained `unit-tests.log`, `build.log` and `browser-tests.log` are earlier runs. The first native Comparator/exporter build passed 21 jobs, recorded in `comparator-build.log`. The original macOS signed-service verification and integration attempts exited 78 at Linux preflight; their logs are in `baseline-attempt/` and `integration/`.

The later Linux verification worker checks above used Palomar’s own isolated judge, not the custom signed-admission worker. That worker’s image build, live isolation probes and full commissioning suite remain untested. GitHub Actions dispatch, signing and publication against a protected repository have not run. The signed registry remains empty; the four catalogue entries have their own explicit verification labels and linked evidence.

## PR #6 independent verification — 2026-10-10

- Akash Levy's exact `10499/12000` bound: **PASS** at `2026-10-10T13:35:18.422104+00:00`. Reviewed PR head: `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`; proof source: `ec626ec9c0e7ab7b29f6c916314932caeb4df39a`.
- The PR subsequently advanced to merge commit `28da98fe20ccf43adeeb2dcb8fc192bb9cfc6209`, incorporating the same main revision. [The follow-up review](pr6-20261010-review.json) checked all 302 package files at that commit against the independently verified hashes: every byte is unchanged. The original kernel receipt remains unchanged and applies to that identical proof content; this comparison is not represented as a second kernel run.
- Rebuilt all 228 submitted Lean modules and 2,670 modules of the pinned dependency fork in the offline Linux sandbox. Real isolation probes and matching, mismatched and ill-typed checker controls passed. The trusted canonical challenge was exported before candidate execution.
- Comparator accepted the all-Dirichlet, zeta and Eisenstein Hecke statements and definitions. Lean, NanoDa and con-ron accepted the exports with only `propext`, `Classical.choice` and `Quot.sound`. The separate contract audit confirms that only the rational literal replaces the upstream `7/8` in the all-Dirichlet statement.
- [Receipt and evidence](../public/proofs/akashlevy-20261010-safe-replay/), [acceptance log](../public/proofs/akashlevy-20261010-safe-replay/logs/judge.log), and [reproduction instructions](../verifier/akashlevy/README.md). Receipt SHA-256: `487e7118c8b7479d8711e03e039e4446abceadfa84f520525b515bd271a9ff82`. Collection used authenticated SSH; hashes were checked locally against the outside-sandbox receipt. Publication neutralizes two diagnostic paths and preserves the receipt bytes.
- The build gate binds all 302 submitted package files to this acceptance. A regression test changes a proof to `True.intro`, regenerates its publication checksums, and confirms that stale acceptance is rejected. The original author-side macOS report and source package remain unchanged as historical evidence.
- `npm run check`: **69 tests passed**, publication/privacy checks passed, TypeScript and production build passed. This includes the eight Python ingestion/contract tests invoked by the Node suite.
- Desktop/mobile browser suite: **17 passed, 1 intentionally skipped** (persistent labels are omitted on narrow screens). Selection, filters, zoom, exact fractions, receipt links, download paths and mobile layout were exercised; screenshots were inspected.
- Production build under `/QuasiRiemannTracker/`: **PASS**, including six dots, all checked evidence links and archive hashes, with no browser errors.

This is a maintainer mechanical replay using a separately approved canonical library and pinned official dependency archives, not a cache-free bootstrap or signed registry admission. It does not commission the separate submission service described above. The preparation remains uncommitted on the latest PR head; no changes have been pushed, published or merged into main by this review.
