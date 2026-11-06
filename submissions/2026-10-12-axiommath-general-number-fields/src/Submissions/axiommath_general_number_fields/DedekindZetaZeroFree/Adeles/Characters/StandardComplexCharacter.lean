/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/StandardComplexCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting

noncomputable section

open scoped Classical ENNReal

namespace DedekindZetaZeroFree.TraceHaarTransport

@[expose] public def standardComplexParameter : ℂˣ :=
  Units.mk0 ((4 * Real.pi : ℝ) : ℂ) (by
    exact Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Real.pi_pos).ne')

public theorem standard_complex_mass :
    KPCplxCharacterHaar.characterHaar standardComplexParameter =
      (2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea := by
  unfold KPCplxCharacterHaar.characterHaar KPCplxCharacterHaar.characterScale
    standardComplexParameter
  simp only [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)]
  have h : (4 * Real.pi) / (2 * Real.pi) = (2 : ℝ) := by
    field_simp; ring
  rw [h]
  norm_num

end DedekindZetaZeroFree.TraceHaarTransport

end
