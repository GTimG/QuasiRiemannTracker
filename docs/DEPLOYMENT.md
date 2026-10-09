# Publish with GitHub Pages

The website and full Lean development are in [GTimG/QuasiRiemannTracker](https://github.com/GTimG/QuasiRiemannTracker). GitHub Pages is configured to publish through GitHub Actions at [gtimg.github.io/QuasiRiemannTracker](https://gtimg.github.io/QuasiRiemannTracker/). The [deployment workflow](https://github.com/GTimG/QuasiRiemannTracker/actions/workflows/ci.yml) records build and deployment status.

## Setup for another repository

1. Use the intended GitHub repository. For a new repository, an empty repository avoids conflicts with generated README/license files. Existing repositories should be inspected and integrated without overwriting their content.
2. Run `npm run configure-repository -- https://github.com/OWNER/REPO` to set the site's source and contribution links. Commit the prepared project, including `proofs/`, `catalogue/` and `.github/`; exclude `.work/`, `node_modules/`, caches and credentials as specified by `.gitignore`.
3. In GitHub, open **Settings → Pages → Build and deployment → Source → GitHub Actions**. Use the repository's default branch (the workflow starts with `main`; update its branch filter if necessary).
4. Configure branch protection or a ruleset requiring pull requests and the **test** job from **Trusted project checks**. Fill `.github/CODEOWNERS` with actual maintainers. Protect the `github-pages` environment so only the default branch deploys. Keep deployment automatic after reviewed merges; a required deployment approval would add a manual step.
5. Push the reviewed initial version. The workflow installs dependencies, checks catalogue and proof integrity, authenticates any signed records, runs tests, builds the site, tests desktop/mobile interactions, uploads `dist/`, then deploys to Pages. The Actions deployment reports the website URL.

GitHub's Pages configuration supplies the correct Vite base path, so repository URLs such as `https://OWNER.github.io/REPO/` work, including proof downloads and JSON data. A custom domain can be configured later through Pages settings.

## Everyday contributions

**Pull request → automatic site checks → maintainer review and merge → automatic deployment.** The public site updates once the build and deployment finish, typically within a few minutes. No local copy/upload step is needed after each merge. Pending external results are welcome in the catalogue with accurate evidence labels. A website CI pass does not prove a mathematical result or upgrade its verification status.

The contributor route is documented in `CONTRIBUTING.md`. Raw Lean submissions are not executed by the site build or by a persistent Ada runner. New native Lean verification is performed separately on Linux verification worker under the project's existing authorization. The optional stricter Comparator + NanoDa service retains its isolated, protected workflow and is not enabled merely by deploying the site.

## What is included

The repository contains readable Lean sources, exact independent targets, pinned reconstruction scripts, original input snapshots, license/attribution records, sanitized compiler logs and verification evidence. The site offers a compressed download of that development. Compiler binaries and third-party source checkouts are reconstructed from recorded pins, not committed. Credentials, runtime sessions, unrelated projects and downloaded caches are excluded.

Published logs and audit metadata are sanitized derivatives: internal paths and worker labels are replaced, and operational handoffs/session records are omitted. Mathematical sources and the retained manuscript inputs are unchanged. See `proofs/qrh-20261009/PUBLICATION.md`. Some older audit files record historical partial statuses. Use `proofs/qrh-20261009/audit/FINAL_STATUS.md` and `final-verification.json` for the final proof status. The manuscript remains unchanged, including its blank author field; website credits identify Tim Gehrunger as maintainer and ProofCouncil as the project.

## Alternative: Netlify

If you prefer the hosting used by the reference site, connect this GitHub repository to Netlify with build command `npm run build`, publish directory `dist`, and production branch `main`. Git-connected Netlify also offers PR previews. The included GitHub Pages workflow is the default here; use only one production deployment destination unless deliberately configuring both.

Official setup: https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages and https://vite.dev/guide/static-deploy.html#github-pages .
