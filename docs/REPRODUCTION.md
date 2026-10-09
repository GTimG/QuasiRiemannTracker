# Completed local Palomar mechanical recheck

On 9 October 2026, the ProofCouncil and original OpenAI proofs passed the same
exported-proof judge and three kernels used by Palomar. Retained evidence and
exact reproduction drivers are under `public/proofs/palomar-20261009/`; read its
`README.txt` for tool versions and the distinction from formal registration.
These Linux verification worker runs used existing pinned proof sources, not the signed worker image
below. The original source/compiler snapshot remains unchanged.

# Earlier signed-service commissioning attempts

# Reproduction and dependency updates

## This environment

The current host is macOS ARM64, with Lean 4.34.1 installed and no running Docker daemon. We did not start Docker, create a VM, use another research machine or modify existing runs. `npm run verify -- submissions/openai-baseline` and `npm run test:integration` both exited 78 at the Linux preflight. See retained attempt logs and summary. The native Comparator/exporter build completed 21 jobs; no fake sandbox was used.

## Construct the isolated worker

Use a fresh disposable Linux VM with rootless Docker, cgroup v2 resource enforcement and Landlock ABI >= 6. Install no credentials or production access. Allow sufficient disk/RAM and build time: the OAI baseline import closure has 2,924 modules. The runtime currently allocates 24 GiB memory including a private 20 GiB scratch ceiling; large proofs may exceed it, in which case raise limits only through infrastructure review and rerun commissioning.

Run from a reviewed, immutable QRH Bounds revision, **without candidate changes**:

```sh
docker build --file worker/Dockerfile --tag qrh-worker:commissioning .
docker image inspect --format '{{.Id}}' qrh-worker:commissioning
```

The build uses pinned upstream sources, official base-image digests and lockfiles; fetches the approved dependencies/cache online; and builds the focused proof closure before sealing it. It never compiles a submission. Comparator's source toolchain selector is changed from 4.34.0 to 4.34.1, which built successfully natively here. NanoDa's export format range matches the exporter in source, but full compatibility is an acceptance gate, not assumed.

The image tag is only a build convenience. Pass the exact inspected `sha256:...` image ID, which must already exist locally (`--pull=never`). Do not pass tags. Do not substitute a fake Landrun script, skip NanoDa, disable seccomp or reuse a writable `.lake` volume.

```sh
npm ci --ignore-scripts
npm run verify -- submissions/openai-baseline --image sha256:ACTUAL_IMAGE_ID
npm run test:integration -- sha256:ACTUAL_IMAGE_ID
```

Every negative fixture must be nonaccepted without timing out or crashing, and the positive baseline must be accepted. Review retained logs to confirm rejection is due to the intended mathematical defect, not an unrelated elaboration/setup error. The suite cannot certify the absence of every generic exit-1 crash; maintainers must inspect diagnostics.

Retain complete `evidence/integration/`, baseline attempt logs, the image-build log and image ID in the acceptance review. Configure real public keys/repository/maintainers and the worker image in `verifier/trust-policy.json` in a separate infrastructure PR. Generate Ed25519 keys with `openssl genpkey -algorithm ED25519`; private keys belong only in the corresponding protected signing environments, never in the worker, source tree or artifact. Set `QRH_PUBLICATION_KEY`/`QRH_PUBLICATION_KEY_ID` only in the trusted commissioning environment, run `node verifier/commission.mjs`, then review/pin the resulting acceptance digest and current `PIN_DIGEST` in the policy. The command refuses missing baseline/suite evidence.

This initial project contains **no fabricated image ID, signing key, repository slug or acceptance certificate**.

## Updating dependencies

1. Use a separate maintainer infrastructure PR, never a proof-submission PR. Resolve real 40-character commits and compare upstream licenses, challenge changes, toolchain, exporter format and NanoDa parser compatibility.
2. Update `pins.json`, hash-checked upstream template if intentionally versioning the contract, dependency manifests, image recipe, lockfiles and notices together. Retain every old receipt and its historical pins.
3. Build a new image from trusted sources. Do not pull untrusted build artifacts from submission runs. Repeat the full baseline and negative suite plus network/filesystem/process isolation probes. Check logs for the intended failures.
4. Invalidate the previous commissioning certificate for **new** verifications; review/sign a new one bound to the new pins/image. Historical records need a versioned policy/verifier migration before a static rebuild with different current pins; this initial version deliberately fails closed instead of silently reinterpreting old records.
5. Review the updated supply-chain and sandbox assumptions. Rotate keys by adding reviewed public keys and retaining old ones for historical signature verification; never rewrite old signatures.

Do not use `lake update` or a floating `main` in a checking job. Source/library upgrades require the full acceptance procedure. Production CI and Linux integration remain to be commissioned outside this host.
