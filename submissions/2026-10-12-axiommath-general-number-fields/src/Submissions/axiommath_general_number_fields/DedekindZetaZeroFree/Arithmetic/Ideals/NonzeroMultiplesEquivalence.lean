/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/NonzeroMultiplesEquivalence.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

@[simp]
theorem nonzero_bottom_multiples_eq_empty (F : Type*) [Field F] [NumberField F] :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (⊥ : Ideal (𝓞 F)) ∣ I} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro I ⟨hI, hdvd⟩
  exact hI (zero_dvd_iff.mp hdvd)

end DedekindZetaZeroFree.LargeSieve
