/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/CharacterBounds/AdmissibleIdealRanges.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def idealAdmissibleFinset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) : Finset (Ideal (𝓞 F)) :=
  (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).filter (fun I => Squarefree I ∧ I ⊔ c = ⊤)

noncomputable def paperShell (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) : Finset (Ideal (𝓞 F)) :=
  (idealAdmissibleFinset F c (2 * T)).filter (fun I => T < (Ideal.absNorm I : ℝ))

theorem mem_idealAdmissibleFinset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (I : Ideal (𝓞 F)) :
    I ∈ idealAdmissibleFinset F c X ↔
      Squarefree I ∧ I ⊔ c = ⊤ ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealAdmissibleFinset, Finset.mem_filter, DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  tauto

theorem mem_paperShell (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) (I : Ideal (𝓞 F)) :
    I ∈ paperShell F c T ↔
      Squarefree I ∧ I ⊔ c = ⊤ ∧ T < (Ideal.absNorm I : ℝ) ∧
        (Ideal.absNorm I : ℝ) ≤ 2 * T := by
  rw [paperShell, Finset.mem_filter, mem_idealAdmissibleFinset]
  tauto

end DedekindZetaZeroFree.LargeSieve.Sieve
