import Candidate.Cycle63.Physical.InitialMass.SecondHighCoordinates
import Candidate.Cycle63.Physical.MarkedHighLedger
import Candidate.Cycle63.Physical.InitialMass.MarkedOrientedHigh
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry

/-- The HIGH exponent value of the actual coordinates of a label is the side exponent, the frequency and volume losses
and the joint excess of the label. -/
theorem actual_high_coordinate_excess_identity (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂)) (Z δ M A a ξ reserve ε : ℝ) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let _q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let _m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)=
      S+(1-ρ)*ω+ρ*ε+Cycle63.Physical.highJointExcess M A a δ c d p R E
        (max (3*c-5*d-R) 0/6) Lc
        (Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)) b₂
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  dsimp only
  dsimp [highExponentValue,actualHighCoordinates,Cycle63.Physical.highJointExcess]
  rw [actual_missing_log left l hC Z]
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)];ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  linear_combination hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))

/-- The HIGH coordinates of an actual label in its physical orientation pay the parent's reserve
`M (1 - ρ) - δ A - a (5 - 6ρ)` and the cone rate of the bin on both removed widths; the bound exceeds the old side
exponent by the label's surplus, which the balanced side exponent carries. -/
theorem actual_high_coordinate_allocation_payment_reserve (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z δ M A a ξ reserve ε : ℝ)
    (hZ : 1 < Z) (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3/4) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S+ValuationCone.surplus c d p R-(M*(1-ρ)-δ*A-a*(5-6*ρ))-
        ValuationCone.commonRate δ*(c+b₂)+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_joint_allocation_saving_oriented_reserve reflected second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ M A a hZ hδ
  have hid := actual_high_coordinate_excess_identity reflected (!reflected) second l hC C₂ D₂ U Z δ M A a ξ reserve ε
  dsimp only at hid hh ⊢
  rw [hid]
  unfold Cycle63.Physical.highJointExcess
  linarith only [hh]

/-- The HIGH coordinates of an actual label in its physical orientation pay the HIGH reserve and the
cone rate of the bin on both removed widths; the bound exceeds the old side exponent by the label's
surplus, which the balanced side exponent carries. -/
theorem actual_high_coordinate_allocation_payment (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (_hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (_hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S+ValuationCone.surplus c d p R-M*Cycle63.Physical.highMainReserve b δ-
        ValuationCone.commonRate δ*(c+b₂)+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_coordinate_allocation_payment_reserve reflected second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ M A a ξ reserve ε hZ hδ
  have hr := Cycle63.Physical.highMainReserve_le_reserve hδ hA ha
  dsimp only at hh ⊢
  linarith only [hh, hr]

end
end OAI.SevenEighths.Cycle63InitialMass
