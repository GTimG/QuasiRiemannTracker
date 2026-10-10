# Argonaut source and independent reproduction

Use the [maintainer sandboxed replay](../../verifier/argonaut/README.md) for
current reproduction. The original native scripts in the historical dossier
are unsafe entrypoints for untrusted submissions. They remain unchanged to
preserve the recorded hashes. The original licensed proof bytes are unchanged.


The independent maintainer replay first passed at **2026-10-10T10:09:10.743884+00:00**.
A repeat with the final guarded collector passed at **2026-10-10T10:24:03.440435+00:00**.
Both runs rebuilt all 152 selected modules inside genuine offline Linux
isolation and passed Comparator, Lean, NanoDa and con-ron for the exact
all-Dirichlet, zeta and finite-order Eisenstein Hecke targets. Only `propext`,
`Classical.choice` and `Quot.sound` were allowed. The trusted challenge was
exported before candidate execution, and receipts were written outside
candidate-writable paths. The current runner also rejects diagnostic symlinks
and oversized logs before collecting evidence.

The [final receipt](../../public/proofs/argonaut-20261010-safe-replay/result.json),
[kernel log](../../public/proofs/argonaut-20261010-safe-replay/logs/judge.log),
[contract audit](../../public/proofs/argonaut-20261010-safe-replay/contract-audit.json),
[control transcripts](../../public/proofs/argonaut-20261010-safe-replay/controls/control-results.json)
and [first acceptance](../../public/proofs/argonaut-20261010-safe-replay/earlier-acceptance/result.json)
retain the independent evidence. The catalogue preserves the first successful
verification time. Its announcement date and exact bound are unchanged.

These runs reuse 7,026 authenticated source-built dependencies and 4,807
hash-pinned official-cache modules, with the pinned toolchain. They do not
claim an empty-cache bootstrap, a production submission service or signed
registry admission. The original proof text and licensed package are unchanged.

The exact source is Argonaut Math's `3499999/4000000` result at commit
[`5971383edcb0b1cf863927eed3b359d2d3ba346e`](https://github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary/tree/5971383edcb0b1cf863927eed3b359d2d3ba346e).
This directory documents independent reproduction; it does not claim a new bound.

The [licensed compact source archive](../../public/proofs/argonaut-20261010-kernels/source-public.tar.gz)
contains the exact original proof additions, notices, dependency pins and an
immutable hash-checked fetch/reconstruction route for the full original release.
See the [package instructions](../../public/proofs/argonaut-20261010-kernels/README.txt)
and [publication audit](../../public/proofs/argonaut-20261010-kernels/source-package-review.json).
No earlier proof snapshot has been changed.

The contributor’s historical report records that Comparator and all three
independent kernels accepted the original all-Dirichlet,
zeta and finite-order Eisenstein Hecke targets at
`2026-10-10T02:21:37.471247+00:00`. The exact statements and their definitions were
compared with a separately compiled canonical challenge, with only `propext`,
`Classical.choice` and `Quot.sound` permitted. Positive, mismatched-statement and
ill-typed controls passed. The [actual report](../../public/proofs/argonaut-20261010-kernels/result.json)
and [full checker log](../../public/proofs/argonaut-20261010-kernels/judge.log)
retain the independent run. This is local mechanical verification proposed for
maintainer review; it creates no signed receipt or Palomar registration.

The contributor’s historical native reproduction compiled 152 modules freshly over 13,669 individually
source-matched cached modules and passed both original Argonaut theorem/axiom
audits. Its inventory contains 13,821 main `.olean` files and 21,488 private/server
sidecars, 35,309 compiled objects altogether. Import resolution was checked
before and after the independent run. The [compiler-input supplement](../../public/proofs/argonaut-20261010-kernels/compiler-input-supplements.json)
binds the shared official-cache and compiler-release provenance audits, including
the independent canonical definition build. Argonaut's native inventory already
included the compiler's implicit `Init` modules.

The [historical reproduction instructions](../../public/proofs/argonaut-20261010-kernels/README.txt)
give the exact release fetch, source reconstruction, checker configuration and
launch command. They refer to the [published baseline setup](../nielstron-20261009-tightening/README.md)
and [checker setup notes](../../public/proofs/nielstron-20261009-kernels/README.txt).
A separate fresh directory fetched the pinned original release and matched all
12,055 restored overlay files, then replayed the original audits using authenticated
compiled artifacts. The full public bootstrap and candidate dependency build have
not been repeated from an empty cache; the recorded native build explicitly reused
audited dependencies. Original source and compiled-artifact inventories are
retained losslessly in bounded, authenticated metadata chunks, with a reconstruction
script and both original and portable-path hashes.
