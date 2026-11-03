/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/LocalEuler/UnitCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Moments.Principal.EulerProducts.WeightedCoefficients
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Kummer.SexticFrequencyCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.AllRowEuler.UnitCovariance

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def residueCoefficient (σ : F →+* ℂ) (I : A.Exterior) (u : A.R) : ℂ :=
  A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) u)

theorem residueCoefficient_eq (I : A.Exterior) (u : A.R) :
    residueCoefficient σ I u = σ (A.sexticResidue I u) := by
  simp only [residueCoefficient, SArithmeticData.sexticResiduePowerChar,
    SArithmeticData.sexticExponent, show (1 : ℤ) % 6 = 1 from rfl,
    Int.toNat_one, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) u)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]

theorem residueCoefficient_norm_of_isUnit (I : A.Exterior) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) u)) :
    ‖residueCoefficient σ I u‖ = 1 := by
  rw [residueCoefficient_eq]
  change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ = 1
  rw [← hu.unit_spec, MulChar.ofUnitHom_coe]
  have hp := A.sexticResidueFamily_normalized.1 I hu.unit
  have hp' : σ ((A.sexticResidueFamily I hu.unit : Fˣ) : F) ^ 6 = 1 := by
    rw [← map_pow]
    simpa using congrArg (fun u : Fˣ => σ (u : F)) hp
  exact Complex.norm_eq_one_of_pow_eq_one hp' (by decide)

end DedekindZetaZeroFree.AllRowEuler.UnitCovariance

end
