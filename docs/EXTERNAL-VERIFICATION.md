# Reproducing an external catalogue result

An external result can move from `verification-pending` to `framework-verified`
after its exact statements and definitions pass Comparator and the exported
proofs pass Lean, NanoDa and con-ron. The only permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`. A native build or website test is insufficient.
These are local mechanical checks proposed for maintainer review; they create no
signed tracker receipt or Palomar registration.

Current maintainer reproduction routes are the [isolated Liu runner](../verifier/liu/README.md)
and [isolated Argonaut runner](../verifier/argonaut/README.md). Both freeze the
canonical challenge before candidate execution and write receipts outside
candidate-writable mounts. Argonaut's verified status requires its own reviewed
maintainer receipt; its earlier submitted native logs cannot grant that status.
Historical dossiers remain immutable, including their unsafe native scripts.

Keep the existing catalogue identity, authors, original publication date and
exact bound. Set `first_verified_at` to the actual independent check completion
time. Liu's algebraic expression must remain the checked target; its certified
rational enclosure is only a plotting coordinate.
Repeating a successful check must not move that first-verification time forward.
An earlier maintainer acceptance can supply it only when its authenticated
receipt, executed driver and kernel log bind the same source revision/content,
target statements, dependencies, tools, isolation guarantees and checking scope.
The latest receipt remains mandatory for the current replay driver.

## Evidence package

Each reviewed run has a new immutable directory under `public/proofs/`. Its
`collection.json` has `schema_version: 1`, kind
`local-mechanical-kernel-evidence`, and a `files` map from relative paths to SHA256
digests. Every file except `collection.json` itself must occur exactly once in
this inventory. Symlinks, unsafe paths and unlisted files are rejected.

The reviewed files `core/external-kernel-pins/<entry-id>.json` bind the **collection's own
digest**, repository, source commit, exact bound, catalogue entrypoint, canonical
challenge digest, source input manifest and checker versions. An entry with null
pins must remain pending. Separate pin files let verification PRs merge independently. A contributor cannot acquire a badge by rewriting both
an artifact and its self-reported checksum.

The package includes:

- `result.json`, with the actual acceptance time, exact targets, kernel and axiom
  lists, Comparator/judge exit statuses and all artifact hashes;
- the independently defined challenge, the original solution wrapper, the exact
  Comparator configuration and full acceptance log;
- a matching control accepted by all three kernels, a mismatched statement
  rejected by Comparator, and an ill-typed proof rejected by Lean;
- checker, exporter and compiler commits/binary hashes, the executed driver and
  original reproduction instructions;
- the actual checked source inventory and native source/build integrity audit,
  including the independent challenge's lack of candidate imports;
- original source provenance and license information.

The result uses the target names `QRHPalomar.allDirichlet`, `QRHPalomar.zeta` and
`QRHPalomar.allHecke`. `definition_names` is empty: the statements' actual
definitions are compared, without a replaceable definition mapping. The checked
challenge digest is pinned independently of the submitted solution. Both proof
exports may be omitted from the website because of their size or licensing, but
their actual digests and byte lengths remain recorded and reproducible.

The report path fields `source_inputs`, `native_build_report`,
`source_provenance` and `reproduction_script` identify authenticated artifacts.
The normalized source inventory contains `manifest_sha256` and a `files` hash
map. The native audit contains `status: "PASS"`, the same
`source_manifest_sha256`, `sources_and_oleans_rehashed: true`, and
`challenge_imports_no_candidate: true`; each claim needs its retained underlying
build/audit evidence. These summaries do not replace the actual checking run.

## Source rights and reproduction

Two publication modes are supported. `archived-source` retains a licensed source
archive, its exact digest and the license/notices. `remote-source` retains a
pinned source inventory and an original fetch/reconstruction script instead.
The latter mode must not redistribute candidate Lean files, source archives or
exported proof graphs; only the original independent challenge and wrapper Lean
files may be published. A public repository without a license does not grant
redistribution permission. Source availability and successful verification are
distinct from the right to copy the source into this website.

Published proof snapshots and earlier checker evidence remain immutable. The
site validator authenticates the reviewed package without executing Lean or
third-party scripts. Heavy reproduction stays outside website CI. Run `npm run
check` and `npm run test:browser` for the metadata, evidence bindings and UI after
the checking work is complete.
