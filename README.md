# QRH Bounds

[Website](https://gtimg.github.io/QuasiRiemannTracker/) · [Contribute](CONTRIBUTING.md) · [Lean formalization](proofs/qrh-20261009/)

A static React/TypeScript dashboard for uniform all-Dirichlet nonvanishing bounds, with exact constants, source links, proof downloads and a GitHub contribution workflow. Apache-2.0 for the new website and Lean development; upstream notices are retained.

The main graphic includes **OpenAI, ProofCouncil, Argonaut, Baiying Liu, Nielstron and Akash Levy**. Current verification statuses and links to the corresponding checking evidence are recorded in the [reviewed catalogue](catalogue/results.json). Pending points are shown as hollow amber dots and contribute to the progress line, which tracks the best listed bound. Verification labels remain separate. These labels describe our evidence, not the validity of other authors’ work.

The complete Linux verification worker development is in [`proofs/qrh-20261009/`](proofs/qrh-20261009/), with 201 local Lean modules, immutable manuscript inputs, pinned dependencies, license records, independent statements and build logs. The source closure of 7,227 modules passed, using matching previously source-built dependencies; the final proof source and audits were rechecked. Both our proof and the original OpenAI 7/8 proof also passed Palomar’s mechanical verifier locally, including Comparator and the Lean, NanoDa and con-ron kernels. Reports, exact statements, tool hashes and logs are in [`public/proofs/palomar-20261009/`](public/proofs/palomar-20261009/). This is separate from Palomar registration or editorial review. The separate signed **Comparator + NanoDa admission service remains uncommissioned**, and its registry remains empty. No signed receipt has been invented or acceptance rule relaxed.

Open a pull request, let site checks pass, and merge it. The workflow automatically deploys the tested website from `main` to GitHub Pages. See [deployment details](docs/DEPLOYMENT.md).

Nielstron's existing catalogue entry is updated to the exact algebraic endpoint;
the earlier N24 source and verification remain available as historical revisions.

Akash Levy's weighted-numerator proof of the exact bound `10499/12000` passed an
independent sandboxed rebuild and Comparator plus three-kernel verification.
Its [independent replay instructions](verifier/akashlevy/README.md) describe the
pinned source, isolated rebuild, checker controls and complete source binding.
The author's original macOS evidence remains an immutable historical report.

## Run locally

Requires Node 22.17 or later.

```sh
npm ci --ignore-scripts
npm run dev
```

Open **http://127.0.0.1:4173/**. `npm run build` checks the complete proof snapshot hashes, validates the catalogue and authenticates the signed registry, then typechecks and generates static `dist/`. No database, login, analytics, remote fonts or live GitHub token is needed by the site.

The dashboard includes selectable points, the exact active record frontier, time-window controls, pan/zoom, keyboard navigation, a focused bound view, an equivalent searchable sortable table, and proof details. Restrict the time window to inspect tiny improvements: the y axis fits the exact rational differences, including differences lost by JavaScript floating-point subtraction.

## Check a proof locally

```sh
npm run verify -- submissions/openai-baseline --image sha256:APPROVED_LOCAL_IMAGE_ID
```

`APPROVED_LOCAL_IMAGE_ID` is deliberately not a fabricated digest: build and inspect the image on Linux as described in [reproduction](docs/REPRODUCTION.md). This command never signs a receipt. It records the attempt and logs under `evidence/baseline-attempt/`. Without a compatible worker it exits **78 (infrastructure blocked)** and performs no Lean checking. This optional signed-service example imports the original OpenAI theorem. Its separate Linux verification worker Palomar check passed; the reports are in `public/proofs/palomar-20261009/openai/`.

## Tests and evidence

```sh
npm test
npm run build
npx playwright install chromium
npm run test:browser
npm run test:integration -- sha256:APPROVED_LOCAL_IMAGE_ID
```

Fast tests verify exact arithmetic, statement generation, manifest validation, path/cache restrictions, signed receipts, exact-head review, immutable history and workflow boundaries. Browser tests cover desktop/mobile selection, zoom, filtering and responsive layout. These tests **do not replace** baseline kernel verification. See [test results](evidence/RESULTS.md), [screenshots](evidence/screenshots/), [native checker build log](evidence/comparator-build.log), and [integration status](evidence/integration/summary.json).

## Project layout

- `src/`, `core/`: dashboard and exact rational arithmetic.
- `catalogue/results.json`: reviewed result metadata and explicit verification statuses.
- `proofs/qrh-20261009/`: full Lean source, reproduction scripts, inputs, audits and logs.
- `public/proofs/qrh-20261009/`: website downloads including the complete source archive.
- `site.config.json`: source and contribution links for `GTimG/QuasiRiemannTracker`.
- `verifier/`: trusted generator, orchestration, receipt authentication and registry tools.
- `worker/`: offline, unprivileged Linux worker recipe and isolation probes.
- `submissions/`: schema-validated manifests, Lean sources, explanations and licenses.
- `registry/verifications/`, `registry/logs/`: immutable authenticated verification journal.
- `registry/records/`, `registry/events/`: publication bundles and signed withdrawal/supersession events.
- `.github/workflows/`: protected maintainer dispatch, isolated checking, separate signing/publication, project tests.
- `tests/fixtures/chart-records.json`: test-only values for chart precision checks; excluded from the website.

## Guides

[Contributing](CONTRIBUTING.md) · [Trust model](docs/TRUST.md) · [Reproduction](docs/REPRODUCTION.md) · [GitHub protections](docs/GITHUB.md) · [Deployment](docs/DEPLOYMENT.md) · [Upstream pins and licenses](docs/SOURCES.md)

Research sources and checks were prepared separately on Linux verification worker. Website deployment uses GitHub Pages; no AWS resources are required.
