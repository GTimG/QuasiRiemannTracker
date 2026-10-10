# Catalogue evidence and signed admission

The main graphic now includes native-Lean-checked results and external formalizations awaiting our independent verification. **Verified in our framework** requires Comparator statement, definition and axiom checks, plus acceptance by Lean, NanoDa and con-ron, with retained source and checking reports. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. On 9 October both our proof and the original OpenAI 7/8 proof also passed Palomar’s unmodified mechanical judge locally: Comparator checked statements and definitions, and Lean, NanoDa and con-ron accepted the exports. The reports and tool hashes are in `public/proofs/palomar-20261009/`. Earlier 7/8 evidence was a corollary; the original proof is now checked directly. This does not constitute Palomar registration or editorial review. **Verification pending** does not allege a mathematical defect. The graph includes pending submissions as amber hollow dots. Its progress line and best-bound summary track verified results only.

The catalogue (`catalogue/results.json`) is reviewed metadata, kept separate from signed registry records. Dates on its timeline are publication/announcement or local verification dates, explicitly identified. Status is the current audit status; no historical verification time is invented. Liu’s algebraic expression is retained exactly.

The complete native Lean snapshot is distributed with hashes, logs and immutable inputs. Build-time hash checking verifies packaging integrity; it does not replay Lean. The separate signed Comparator + NanoDa admission service remains uncommissioned. The policy below still governs that separate admission process, and its requirements are not waived by a catalogue badge.

The weighted-numerator contribution uses the maintainer replay described in
`verifier/akashlevy/README.md`. Its publication gate requires the isolated
run's receipt and all 302 submitted package files to match the reviewed pins,
including all 228 new proof modules and the exact dependency-fork revision.
Changing a proof and regenerating its public archive/checksums cannot retain
verified status. The author's unsandboxed report is historical evidence only;
the contribution's verification time comes from the first successful independent
run. The catalogue build checks this gate as well as the publication checker.

# Trust model and limits

## The mathematical boundary

A contribution must establish the pinned OpenAI all-Dirichlet statement with only `7 / 8` replaced by a normalized rational literal. The challenge is generated from a hash-checked upstream template; submitters cannot supply its predicate, L-function, hypotheses, constant definition, kernel options or permitted axioms. The same `NeZero q`, complex character, complex argument and pole exclusion remain. The trusted wrapper applies the declared proof entrypoint to exactly those arguments.

Comparator extracts the challenge before elaborating candidate imports. It checks statement identity, the definitions used by that statement, transitive proof axioms, and Lean kernel replay. No definition holes are configured. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. `sorryAx`, hidden assumptions and `Lean.trustCompiler` are not allowed. NanoDa is configured on every run, with the same axiom list and hard rejection of unpermitted axioms. Kernel acceptance is joint, never a fallback.

## Execution boundary

Lean elaboration and `.olean` loading are arbitrary untrusted code. Checking must run on a fresh, disposable Linux machine/JIT runner with a rootless container daemon and no host credentials. The orchestrator launches a pinned image ID with:

- a non-root UID, no capabilities, no-new-privileges and a read-only image;
- no network, all socket/socketpair creation denied (including AF_UNIX), and denied ptrace/process-memory syscalls;
- a fresh PID namespace, 256-process limit, four CPUs, 24 GiB memory with no additional swap, and a one-hour watchdog;
- read-only candidate input, private size-limited scratch and temporary files, no daemon socket, secrets, credential directories, devices or shared writable caches;
- a 16 MiB log limit, followed by forced container removal on failure/timeout.

Landrun adds per-child filesystem/execute/IPC restrictions inside the worker. The preflight requires Landlock ABI >= 6 and actively tests denial of network sockets, outside-cache writes and parent-process signaling, while allowing a cache write. AF_UNIX is denied by outer seccomp, covering the socket issue documented by the pinned Comparator README (which uses systemd RestrictAddressFamilies for that purpose). These are real restrictions, not a fake-landrun shim. The seccomp profile is intentionally not presented as independently audited. The Linux kernel, rootless OCI runtime, Landrun and hardware remain in the trusted computing base.

The image's approved library tree is copied into a private scratch directory for each invocation. No writable cache survives a run. Comparator retains the extracted challenge in its parent process before giving the candidate write access to its private `.lake`. It never accepts candidate JSON as a result. The orchestrator owns source bytes, manifest validation, challenge/configuration generation, process status and receipt construction outside the candidate-writable environment.

## Supply chain and provenance

Toolchain, all mathematical dependencies, Comparator, exporter, NanoDa, Landrun and GitHub Actions are pinned. Official base-image digests are pinned in the Dockerfile. Online image construction trusts the official Lean release artifact, apt/Rust/Go package supply chains and the pinned Mathlib cache provider. The **finished image ID** binds the exact built bytes, including dependencies and binaries; commissioning must retain that ID and build logs. This is not a claim that all upstream distribution systems are reproducible or independently authenticated. To remove cache-provider trust, rebuild Mathlib from the pinned sources in a separate image build.

The sign job runs on a different clean runner. It retrieves an immutable GitHub Actions artifact from the same run/attempt after the checking job succeeds, verifies the approved worker acceptance record, pins, log digest and current PR head, then signs an Ed25519 envelope. The artifact service, protected orchestration revision, runner provisioning, GitHub identities and signing-key management are trusted. Candidate-written JSON and console success strings have no authority. The check result is the trusted Comparator process's exit status, which includes both kernels, inside the tested restrictions.

Receipts bind the exact source commit, content inventory digest, manifest/rational, canonical challenge digest/version via pins, dependency/tool versions, worker image, protected orchestration commit, time, statuses and log digest. All successful receipts are archived into a protected append-only, content-addressed journal before publication. The main timeline uses the earliest authenticated success for the exact published source revision. Logs and receipts remain immutable; a separate signed publication record carries submission, merge and publication dates and independent attribution/license review.

A receipt is not automatically a publication. The publication tool re-fetches the PR/reviews, rejects author self-approval, requires an approved current-head maintainer review and a merged PR, checks the merged submission content digest, and binds the publication to the archived earliest receipt. It only prepares a signed bundle for a maintainer registry PR. The static build independently authenticates every bundle and rejects inconsistent logs, unknown predecessors and history changes.

## Failure categories

`accepted`: Comparator exits zero, including mandatory NanoDa, after isolation preflight. It remains unsigned/unpublished until separate gates pass.

`infrastructure-blocked`: unsupported OS, missing approved image/daemon, failed isolation or absent commissioning. No mathematical conclusion.

`timed-out`, `resource-exhausted`, `checker-crash`: no mathematical conclusion. Preserve diagnostics; never convert these into proof rejections or acceptances.

`checking-failed`: nonzero Comparator result. Upstream does not expose an authenticated structured distinction between elaboration error, mathematical rejection, external-kernel failure and every internal error. We deliberately do not diagnose from candidate-controlled output. Logs guide maintainer investigation. Some crashes with generic exit 1 cannot be distinguished automatically; this limitation is explicit.

## What is not yet established

The original macOS attempt only compiled Comparator/exporter and ran website tests. The later Linux verification worker recheck passed both full proofs through Palomar’s separate sandboxed judge and its positive/negative preflight. The custom signed-admission worker image and its commissioning suite remain untested. The commissioning policy has no repository, keys, worker digest or acceptance receipt and therefore admits nothing. No production-ready claim is made.

Two implementations can share conceptual bugs. Kernel correctness, exporter/comparator parsing, trusted template definitions, system isolation and authenticated supply chains remain assumptions. Denial-of-service limits bound a run but do not prove mathematical invalidity. License review and explicit lineage reflect reviewed attribution, not a machine proof of mathematical priority.
