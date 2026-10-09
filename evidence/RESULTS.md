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
