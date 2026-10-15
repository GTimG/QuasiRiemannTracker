import Candidate.Cycle62.Physical.InitialMass.SecondHighPayment
import Candidate.Cycle62.Physical.FinalCapacity.Final

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle62Moment Cycle62FinalCapacity
local notation "O" => HeckeFamily.O

/-- The low-branch nominal energy cancels the actual second normalizer
and the amplified main-radius cost, leaving the first geometry weight.
No count of first labels or residual projectors is hidden in this identity. -/
theorem actual_low_scalar_payment (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve error : ℝ)(hZ : 1<Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error)=Z^(A-c+R+E-b₂+error) := by
  dsimp only
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ]
  unfold secondNominal
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz]
  congr 1
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hh := hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
  linarith

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_low_scalar_payment
