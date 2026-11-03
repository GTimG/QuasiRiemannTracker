/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/ResiduePhases/PhaseDifference.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.CRTRawLocalPhaseAlgebra
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem uniformizer_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : uniformizer C p ≠ 0 := by
  change algebraMap F (LocalField p) (generator C p : F) ≠ 0
  apply (map_ne_zero (algebraMap F (LocalField p))).2
  exact_mod_cast (generator_generates C p).1

theorem phase_difference {K : Type*} [Field K]
    (π S U H d d' v v' r q b : K) (t k J : ℕ)
    (hπ : π ≠ 0) (hS : S ≠ 0) (hU : U ≠ 0)
    (hd : d - d' = π ^ k * r) (hv : v - v' = π ^ t * q)
    (hc : H * π ^ J - U * π ^ t * d = π ^ k * b) :
    ((H * π ^ J - U * π ^ t * d) * v) / (S * U * π ^ (k + t)) -
      ((H * π ^ J - U * π ^ t * d') * v') / (S * U * π ^ (k + t)) =
      (S⁻¹ * U⁻¹) * b * q - S⁻¹ * r * v' := by
  have hd' : d' = d - π ^ k * r := by linear_combination -hd
  have hv' : v = v' + π ^ t * q := by linear_combination hv
  rw [hd', hv', pow_add]
  field_simp [hπ, hS, hU]
  linear_combination π ^ t * q * hc

end DedekindZetaZeroFree.CRTRawLocalPhaseAlgebra

end
