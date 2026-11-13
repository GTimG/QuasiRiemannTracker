/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/TotallyComplexQuadraticSignature.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem quadraticExtension_signature
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hF : NumberField.IsTotallyComplex F) (hdeg : Module.finrank F E = 2) :
    NumberField.IsTotallyComplex E ∧
      NumberField.InfinitePlace.nrComplexPlaces E =
        2 * NumberField.InfinitePlace.nrComplexPlaces F := by
  haveI hFc : NumberField.IsTotallyComplex F := hF
  haveI : NumberField.IsTotallyComplex E :=
    NumberField.isTotallyComplex_of_algebra F E
  refine ⟨inferInstance, ?_⟩
  have hE := NumberField.IsTotallyComplex.finrank E
  have hF' := NumberField.IsTotallyComplex.finrank F
  have hmult : Module.finrank ℚ E =
      Module.finrank ℚ F * Module.finrank F E :=
    (Module.finrank_mul_finrank ℚ F E).symm
  rw [hdeg, hF'] at hmult
  have h2 : 2 * NumberField.InfinitePlace.nrComplexPlaces E =
      2 * (2 * NumberField.InfinitePlace.nrComplexPlaces F) := by
    rw [← hE, hmult]
    ring
  exact Nat.mul_left_cancel (by norm_num) h2

end DedekindZetaZeroFree.LargeSieve
