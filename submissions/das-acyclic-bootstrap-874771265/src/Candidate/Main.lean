/- MIT License

Copyright (c) 2026 Subhanjan Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This notice applies to the files of this submission marked MIT. Files adapted
from Hailey Collet's and Mark Lewko's Apache-2.0 sources retain their original
notices and license. Development was AI-assisted with OpenAI Codex and
Anthropic Claude. -/
import Candidate.Endpoint
import Candidate.TrackerInput

/-!
# Two ordinary-source returns to the all-Dirichlet boundary 0.874771265

The entry point `Candidate.bound` has the repository's all-Dirichlet scope:
for every positive modulus, every complex Dirichlet character, and every complex
argument with real part strictly greater than 174954253/200000000, its L-function
is nonzero, with the original principal-character pole exclusion.

## Exact deduction

The starting full Hecke-family beta bound is 8747729897/10000000000, from the
Collet sources included in the admitted Lewko dependency. Round A returns
87477127/100000000; round B returns 174954253/200000000. Their natural root prices
are respectively 11243189691/2500000000 and 112431381/25000000. Each root price is
6*(2*theta_input-1). The NF theorem's internal reference stays 11243277/2500000.

Each round has 21,527 count transitions and 19,529 physical transitions. Every
transition uses its preceding node as both suppliers. `CoreBridge.sound` maps
the small rational certificate predicate to the original analytic `SourceValid`.
The induction therefore applies the existing NF rule to previously obtained
sources. Allowance, low fee and high fee are 10^-17, 10^-12 and 10^-10.

Each return uses 38 non-old admission windows and 224 physical boxes. Every new
window verifies all fifteen admissibility guards. A single common count scheme,
exact Bernstein identities, positive rational margins, closed-rectangle coverage
and conductor interpolation provide the physical schedule. The original inverse
input has price 2; no improved inverse estimate or Conjecture C is assumed.

## Proof map

* `TrackerInput.admittedInputs`: the concrete existing full-family bound,
  variable-price natural source theorem and fixed-reference NF theorem.
* `GraphAssembly.ACount`, `APhysical`, `BCount`, `BPhysical`: acyclic source graphs.
* `SuppliersA.global_suppliers`, `SuppliersB.global_suppliers`: the global sources.
* `ReturnA` and `ReturnB`: exact geometry, finite admission and row certificates,
  common-envelope covers, schedules and source-to-beta return proofs.
* `Endpoint.first_family_beta`, `Endpoint.family_beta`: the two ordered returns.
* `FamilyTransfer.dirichlet_of_family_beta`: the full-family-to-Dirichlet transfer.
* `Candidate.bound`: the concrete conclusion, with no extra input hypothesis.

The intermediate `Inputs` structure packages existing theorems. It is supplied
by `TrackerInput.admittedInputs` in the final theorem, rather than assumed by it.

## Reproduction and attribution

All rational witnesses and certificate proofs are included as Lean source.
Checking requires the declared admitted dependency and the repository's pinned
Lean, package and verifier revisions. It requires no private archive, floating
point computation, witness-search program or unpublished arithmetic hypothesis.
The repository's canonical statement comparison, permitted-axiom checks and
three-kernel protected verification determine admission of the exact source head.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

Subhanjan Das developed this parameter refinement and formalization, with
substantial AI assistance from OpenAI Codex and Anthropic Claude. Round A follows
the adaptive-cap ordinary-source construction first proposed, as an exact-rational
computation without Lean verification, in rohanarun/quasi-rh-hillclimb PR #28. The
graphs here are regenerated from the variable root price 6*(2*theta_input-1), with
allowance and fees 10^-17, 10^-12 and 10^-10, and every transition is proved in Lean. Hailey Collet's ordinary-source construction, NF
theorem and finite Bernstein return, Mark Lewko's admitted development and generic
return interfaces, and OpenAI's analytic framework retain their attribution and
licenses. Some adapted Apache-2.0 files keep Mark Lewko's original modification
notice ("Modified 2026-10-22 for Mark Lewko private candidate"); it is a retained
provenance notice from the admitted Lewko submission, and everything those files
need is in this submission and its declared public dependency.
-/

set_option autoImplicit false
namespace Candidate

theorem bound {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) {s:ℂ}
 (hs:(174954253/200000000:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) :
 _root_.DirichletCharacter.LFunction χ s≠0 :=
 Das.QRH.Endpoint.dirichlet_nonvanishing Das.QRH.TrackerRebuild.admittedInputs χ s hs hpole

end Candidate
#check @Candidate.bound
#print axioms Candidate.bound
