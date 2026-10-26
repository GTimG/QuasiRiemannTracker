# Independent verification of PR #79

The exact source `3dcd2742e2a605f2f480e46b824cb695d3fc4863` passed at
2026-10-26T18:56:58.020243+00:00 for the all-Dirichlet bound
`4373037/5000000` (0.8746074). The protected generator changes only the rational
constant in the pinned OpenAI statement. All positive moduli, complex Dirichlet
characters, complex arguments, the original pole exclusion and L-function remain.
The intentional `sorry` in [Challenge.lean](Challenge.lean) is a statement
template, never the accepted proof.

The unchanged outside-sandbox [receipt](result.json), SHA-256
`0571399fe05bb67dcb1d2bb074ecea2e453aaa2440d0a04d65929c96f631528e`, binds the
exact source, generated theorem, dependencies, library inventory, checker tools
and artifacts. [judge.log](judge.log) records Comparator acceptance and explicit
acceptance by Lean, NanoDa and con-ron. Only `Classical.choice`, `Quot.sound`
and `propext` were permitted. Fresh preparation from the immutable Git head
matched the checked source contract before registration.

## Build and resource evidence

The previous hosted run exhausted its overall three-hour budget during
compilation. This run compiled all 3,952 uncached modules in 74m02s. It reused
2,923 modules from the protected, signed build cache, whose original index,
signature and public key are retained in [signed-cache](signed-cache).
The restorer matched module, compiler and dependency fingerprints before reuse;
no candidate-provided cache was accepted. The source dependencies are the
submission itself, Hailey Collet's source and OpenAI's baseline, bound by the
tree hashes in [audit.json](audit.json).

For the same 3,513 modules completed by the failed CI run, local compilation
finished in 64m44s versus 2h58m06s, about 2.75 times sooner. Individual
single-thread compilations were slightly slower locally; the gain came from
greater concurrency. The module at which CI exhausted its budget,
`Record12518109Gain.WholeRootMaxima`, passed in 6.5 seconds. See
[compilation-comparison.json](compilation-comparison.json) for the measured
comparison and its scheduling limitations.

The solution wrapper/export phase took 3m16s, and Comparator plus all three
kernels took 30m29s. The complete candidate replay took 1h50m30s. Including
VM startup, setup, the independent baseline and rejection controls, the
container ran for 2h20m44s and exited successfully without an outer OOM or
watchdog timeout.

## Checker and controls

The run used pristine upstream NanoDa 0.4.26 at
[`998e0a84e4c1572ca279ff05007af6ec6639405a`](https://github.com/ammkrn/nanoda_lib/tree/998e0a84e4c1572ca279ff05007af6ec6639405a),
the version used in Tim's PR #69/#76 capacity remediation. A fresh isolated
build passed 54 tests, with no failures and eight upstream documentation tests
ignored. The source manifest, archive digest, Cargo.lock, license, compiler
versions and full build/test logs are in [nanoda-upstream](nanoda-upstream).
The actual binary SHA-256 is
`1d96ec2adb1edbc57ec9b25423f26d9526512e994e8e0b312cdcfc584a1ddd5d`;
all other checker binaries retain their protected pins. This local upgrade does
not change the production verifier's pins, and no diagnostic checker patch was
used. The old checker was not rerun on this exact export.

The real OpenAI 7/8 baseline was freshly replayed with this runtime, including
new exports and all three kernels; [baseline-judge.log](baseline-judge.log)
records acceptance. Confinement, positive proof, mismatched-statement and
ill-typed-proof controls passed. Explicit `sorryAx` and hidden-assumption
fixtures compiled, reached the judge and were rejected without success
receipts. The candidate reran its own sandbox, mount and proof controls.

The protected verifier revision was
`4691ba8e244ff645b2a9082187b1739e940f7e50`. Its sole source change was the
documented [timeout patch](budget-only.patch): shared 3h to 36h, each module
30min to 2h, exports 10min to 2h and final checking 1h to 24h. The actual
[driver](replay-driver.txt) and both runtime manifests are retained. Statement,
axiom, confinement and acceptance rules were unchanged.

## Isolation and provenance

A fresh KVM guest had 12 vCPUs, 48 GiB RAM and an 80 GiB disk inside a nonroot,
read-only Docker container capped at 12 CPUs and 52 GiB without swap. The
container dropped all capabilities and exposed only `/dev/kvm` and its own
anonymous disk volume, with no host directory mounts, Docker socket, host
credentials or published ports. Setup used the restricted proxy. Proof
execution used Palomar's actual unprivileged sandbox with no network,
read-only approved inputs and bounded private scratch. Kernels ran sequentially
to make the larger memory allocation available to each.

The trusted challenge was exported before candidate execution. Sources,
libraries, tools and the challenge remained unchanged. Receipts were generated
outside candidate-writable directories. A root guest collector transferred
selected regular files over a separate bounded virtio-serial channel after
checking; the host validated paths, sizes, hashes and exit states after the VM
stopped. Console text was not treated as proof of success. See
[host-provenance.json](host-provenance.json), [outer-run.json](outer-run.json)
and [independent-review.json](independent-review.json).

[logs.json](logs.json) maps original collected paths to their exact UTF-8 log
contents, without redaction. [log-archive.json](log-archive.json) records their
original byte hashes. [evidence-layout.json](evidence-layout.json) maps the
published files to the collected archive. The complete input ISO, original
archive, VM disk, frozen exports, full library inventory and cache-input
inventory remain on the verification host with their bound hashes.

Compiler/exporter bootstrap and pinned dependency provenance remain part of
the trust model. This independently reviewed local receipt requires protected
exact-head registration and ordinary admission checks before publication.
Authorship and inherited notices in the submission and dependencies remain
unchanged.
