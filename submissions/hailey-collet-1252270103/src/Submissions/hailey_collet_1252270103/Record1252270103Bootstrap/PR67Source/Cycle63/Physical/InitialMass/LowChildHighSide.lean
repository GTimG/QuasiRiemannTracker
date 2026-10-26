import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedHighCoordinates
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedOrientedHigh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The first-level payment of the HIGH coordinates of a label with the first projector radical kept: the coordinates
of a row of the second expansion of a child pay the side exponent of the label without the projector, less the
parent's reserve. Released under Apache 2.0. -/
set_option autoImplicit false
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
open CenteredMomentFirstCanonicalAllowance CenteredMomentCommonHarmonicMass
open Cycle63FinalCapacity CenteredMomentFirstPhysicalSource CenteredMomentAmplificationChildSourceCaps

/-- The balanced HIGH saving of an actual label in its physical orientation, with the parent's reserve
`M (1 - ρ) - δ A - a (5 - 6ρ)` kept and with the logarithm `E` of the first projector radical kept as a saving: the
saving of `actual_high_joint_allocation_saving_oriented_reserve` is the same inequality with `E` thrown away, and its
left side contains `-E`, so the right side may keep `-E` as well. -/
theorem actual_high_joint_allocation_saving_oriented_reserve_E (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z δ M A a : ℝ)
    (hZ : 1 < Z) (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3/4) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂-ValuationCone.surplus c d p R ≤
        -(M*(1-ρ)-δ*A-a*(5-6*ρ))-ValuationCone.commonRate δ*(c+b₂)-E := by
  dsimp only
  obtain ⟨hρlo,hρhi,_⟩ := Cycle63.Physical.high_density_bounds hδ
  have hcommon := ValuationCone.actual_first_common_saving reflected l hC hD heq Z
    (LocalMoment.unmarkedDensity δ) δ hZ (by linarith) (by linarith [Cycle63.Arithmetic.rho0_bounds.2])
  dsimp only at hcommon
  unfold ValuationCone.firstCommon at hcommon
  have hb₂ : 0 ≤ Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hg₂ : Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  have hγ : ValuationCone.commonRate δ ≤ δ := by
    unfold ValuationCone.commonRate
    linarith [le_max_left (3/19:ℝ) (4*LocalMoment.unmarkedDensity δ-5/4)]
  change _≤-ValuationCone.commonRate δ*_-_ at hcommon
  have ht₂ := actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ
  have hsecondgap := mul_nonneg (show 0 ≤ δ-ValuationCone.commonRate δ by linarith) hb₂
  linarith only [hcommon, hg₂, ht₂, hsecondgap]

/-- The HIGH coordinates of an actual label in its physical orientation pay the parent's reserve and the cone rate of
the bin on both removed widths, and the side exponent of the label without its first projector: the bound is the
side exponent `p + (A - c + R + E + B) + surplus` of `actual_high_coordinate_allocation_payment_reserve` less the
logarithm `E` of the first projector radical. -/
theorem actual_high_coordinate_allocation_payment_reserve_E (reflected second : Bool) (l : FirstSourceLabel)
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
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    highExponentValue δ (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z M A a ξ reserve ε)≤
      (p+A-c+R+max (3*c-5*d-R) 0/6+ValuationCone.surplus c d p R)-(M*(1-ρ)-δ*A-a*(5-6*ρ))-
        ValuationCone.commonRate δ*(c+b₂)+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_joint_allocation_saving_oriented_reserve_E reflected second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ M A a hZ hδ
  have hid := actual_high_coordinate_excess_identity reflected (!reflected) second l hC C₂ D₂ U Z δ M A a ξ reserve ε
  dsimp only at hid hh ⊢
  rw [hid]
  unfold Cycle63.Physical.highJointExcess
  linarith only [hh]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
