# Verification of the quartic boundary

The public statements are in `evidence/multi-kernel/Challenge.lean`; their
proofs are in `Solution.lean`. The challenge imports the pinned original
L-function definitions and moment presentation, without importing a Cycle25
theorem. Comparator checks the statements and their definitions against the
solution. The only permitted axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The seven checked roots are:

| Declaration in `Cycle25Verification` | Statement |
| --- | --- |
| `allDirichlet` | Every positive modulus and every complex Dirichlet character, at rational θ = 683505193/781250000, with the principal pole excluded |
| `zeta` | Riemann zeta in the same strict half-plane, away from its pole |
| `allHecke` | The full finite-order, trivial-infinite-type Eisenstein Hecke family at that rational boundary, with the principal pole excluded |
| `exactAllDirichlet` | The corresponding result at 11/12 − ℓ/4 for the quartic root ℓ in [1/6, 1/5] |
| `exactZeta` | Zeta at the exact quartic boundary |
| `exactAllHecke` | The full Hecke family at the exact quartic boundary |
| `plainMoment` | The common-prime-profile positive-slot moment at 7/10 ≤ κ ≤ 3/4, with β ≥ 51/100 and 2β − 1 ≤ κ and the stated arithmetic and smoothness conditions |

The moment challenge spells out its mesh definition and full contract.
Independent plain profiles and height twists remain permitted; the prime
slots share a smooth profile and use individual fixed ray-character
coefficients. This theorem does not assume the new quartic nonvanishing bound.

## Recorded checks

The contributor run completed successfully on October 10, 2026. Official
Comparator accepted the exact statements and definitions; Lean, NanoDa and
con-ron each accepted the proof. con-ron checked 124,306 declarations.
The full compile/export/judge sequence took 836.547 seconds. See
`evidence/multi-kernel/result.json` and `judge.log`.

The fresh source build compiled all 298 Cycle25 modules in the endpoint's
import closure and the three reused moment modules: 301 modules in total,
against pinned dependency caches. The 2,923 unmodified OpenAI modules were
authenticated against their pinned sources and their compiled cache was
reused for this build. This is a fresh build of the new proof and reused
moment, rather than a claim to have rebuilt Mathlib and OpenAI from scratch.

The ordinary Lean dependency audit independently checks the exact endpoint
and its Hecke, Dirichlet and zeta corollaries, including their transitive
axioms. It also checks that the modified analytic path does not invoke a
previous improved nonvanishing endpoint. The original 7/8 initialization
is an explicit permitted dependency.

The kernel run includes three controls: a matching proof must pass, a changed
statement must fail comparison, and an ill-typed proof must fail checking.
The complete exported proof closures are checked, including inherited
declarations reached by these seven roots. Specification `sorry` placeholders
in `Challenge.lean` are intentional; the solution is subject to the axiom
restriction above.

## Reproduction and evidence

Use `REPRODUCE.md` to build the source package, then follow
`evidence/multi-kernel/README.md` to reproduce the independent check.
The source compiler is Lean 4.34.1. The judge is the official Linux
Lean 4.35.0-rc2 bundle with Comparator, NanoDa and con-ron; exporter and
helper revisions are pinned in the evidence.

The checker used its kernel sandboxes and bounded cgroup supervision, with
32 GiB memory maximum, 1 GiB swap maximum and four CPUs. No GPU was used.
Source and tool hashes were checked before and after the run. Large exported
proof files and compiled caches are omitted; their hashes and byte lengths
are retained, and the included source regenerates them.

Publication copies replace private absolute paths with descriptive labels.
`evidence/publication-map.json` binds each copy to the original evidence hash
and records whether its bytes changed. The proof sources and the challenge
and solution wrappers are preserved byte for byte.

These are contributor-run checks. The catalogue entry remains
**verification-pending** for maintainer review; this dossier is not a signed
registry admission receipt.
