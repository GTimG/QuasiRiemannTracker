import Candidate.Cycle62.Physical.InitialMass.SecondHighCoordinates
import Candidate.Cycle62.Physical.MarkedHighLedger
import Candidate.Cycle62.Physical.InitialMass.MarkedOrientedHigh

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle62Moment Cycle62HighGeometry
local notation "O" => HeckeFamily.O

theorem actual_high_coordinate_excess_identity (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)=
      S+(1-ρ)*ω+ρ*ε+Cycle62.Physical.highJointExcess M A a δ c d p R E
        (max (3*c-5*d-R) 0/6) Lc
        (Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)) b₂
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  dsimp only
  dsimp [highExponentValue,actualHighCoordinates,Cycle62.Physical.highJointExcess]
  rw [actual_missing_log left l hC Z]
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)];ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  linear_combination hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))

theorem actual_high_coordinate_allocation_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤7/10) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S-M*Cycle62.Physical.highMainReserve b δ-(c+b₂)/20+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_joint_allocation_saving_oriented reflected left second l hC hD
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a hZ hb hδ hM hA ha
  have hid := actual_high_coordinate_excess_identity reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb ⟨hδ.1,by linarith [hδ.2]⟩ hM hA ha
  dsimp only at hid hh ⊢
  rw [hid]
  unfold Cycle62.Physical.highJointExcess
  linarith only [hh]

theorem actual_high_coordinate_payment_of_reserve (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε μ : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) (hreserve : μ≤Cycle62.Physical.highMainReserve b δ) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S-M*μ+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_joint_excess_oriented_of_reserve reflected left second l hC hD
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a μ hZ hb hδ hM hA ha hreserve
  have hid := actual_high_coordinate_excess_identity reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
  dsimp only at hid hh ⊢
  rw [hid]
  unfold Cycle62.Physical.highJointExcess
  linarith only [hh]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_high_coordinate_excess_identity

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_high_coordinate_allocation_payment
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_high_coordinate_payment_of_reserve
