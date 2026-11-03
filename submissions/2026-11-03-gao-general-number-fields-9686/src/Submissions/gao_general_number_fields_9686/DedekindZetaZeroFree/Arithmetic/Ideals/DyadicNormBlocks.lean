/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/DyadicNormBlocks.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def idealDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) : ℕ → Finset (Ideal (𝓞 F))
  | 0 => {⊤}
  | k + 1 => paperShell F c ((2 : ℝ) ^ k)

def dyadicScale : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 : ℝ) ^ k

noncomputable def clippedDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (j : ℕ) : Finset (Ideal (𝓞 F)) :=
  idealDyadicBlock F c j ∩ idealAdmissibleFinset F c X

end DedekindZetaZeroFree.LargeSieve.Sieve
