/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.LabelPayments
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryHighSelected

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open Cycle61FinalCapacity
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry Cycle61InitialMass
open Record12518109Natural QRH.Record12518109Source
local notation "O" => HeckeFamily.O

/-- The complete RAW coefficient, the one missing-radical count and the
sharp row radius give precisely R12 after the original first normalization.
This identity uses no HIGH density and keeps both balanced and projector costs. -/
theorem actual_raw_coordinate_identity (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε εv : ℝ) :
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second
      l C₂ D₂ U Z M A a ξ reserve ε) εv
    x 0+x 1+x 2-labelSide reflected l Z A-labelSurplus reflected l Z=
      rawExcess a (labelR l Z) (labelE l Z)
        (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
        (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
        (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ))
        (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))
        (labelSurplus reflected l Z)+ε+εv := by
  dsimp [childHighCoordinates,actualHighCoordinates,rawExcess,labelSide,labelC,labelD,labelR,labelE,labelP]
  rw [actual_missing_log (!reflected) l hC Z]
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)];ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  linear_combination hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))

/-- Actual second common ideals pay the favorable second term in R15. -/
theorem actual_raw_second_nonneg (second : Bool) (C₂ D₂ : Ideal O)
    (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z : ℝ) (hZ : 1<Z) :
    0≤Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) := by
  have hg : Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  have ht:=Cycle61FinalCapacity.actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ
  linarith

/-- R15 bound on the literal four physical exponent coordinates. The
first-cap expression is unchanged and its whole-slot mesh payment appears once. -/
theorem actual_raw_coordinate_erasure (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε εv q lam B b t f F mesh : ℝ)
    (hZ : 1<Z) (hlam : 1≤lam) (hq : 0≤q) (hf : 0≤f) :
    let c:=labelC reflected l Z
    let d:=labelD reflected l Z
    let R:=labelR l Z
    let Lc:=Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second
      l C₂ D₂ U Z M A a ξ reserve ε) εv
    x 0+x 1+x 2-labelSide reflected l Z A-labelSurplus reflected l Z+
      q*((b-f)-(B*(F+Lc-R-max (c-d) 0)-(t-c+f))/lam+mesh)≤
      -rawGap a q b t B F lam+
        rawCommon R (max (3*c-5*d-R) 0/6) Lc
          (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
          (labelSurplus reflected l Z) q lam c B d+q*mesh+ε+εv := by
  dsimp only
  rw [actual_raw_coordinate_identity reflected second l hC C₂ D₂ U Z M A a ξ reserve ε εv]
  have hE : 0≤labelE l Z := (actual_first_gates (!reflected) l hC hD Z hZ).2.1
  have hs:=actual_raw_second_nonneg second C₂ D₂ hC₂ hD₂ heq₂ U Z hZ
  have he:=raw_low_after_erasure a (labelR l Z) (labelE l Z)
    (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
    (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
    (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ))
    (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))
    (labelSurplus reflected l Z) q lam (labelC reflected l Z) B (labelD reflected l Z)
    b t f F mesh hlam hq hE hs hf
  linarith only [he]

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.actual_raw_coordinate_identity
#print axioms OAI.SevenEighths.Record12518109Raw.actual_raw_second_nonneg
#print axioms OAI.SevenEighths.Record12518109Raw.actual_raw_coordinate_erasure
