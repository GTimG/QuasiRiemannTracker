/- Copyright (c) 2026 Sil. Apache-2.0.
   New uneven common-factor estimate for PR63's actual valuation vectors.
   Prepared with OpenAI Codex assistance. -/
import Candidate.Target830.Source.Valuation
import Candidate.Target830.High.Allocation
import Candidate.Uneven.SkewCone

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OAI.SevenEighths.Target830.Source.Valuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSecondCanonical
open Cycle63Moment Cycle63HighGeometry CenteredMomentCommonSupport
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss
local notation "O" => HeckeFamily.O

theorem sourceExponent_left_eq (i j : ℕ) :
    FirstNumeratorValuation.sourceExponent true i j =
      if (i+5*j)%6=0 ∨ (i+5*j)%6=5 then 0 else 1+(i+5*j)%6 := by
  unfold FirstNumeratorValuation.sourceExponent netExponent
  simp only [Bool.true_eq, if_true]
  split_ifs <;> omega

theorem skew_point_eq (i j : ℕ) : point i j = SkewCone.point i j := by
  simp only [point, SkewCone.point, sourceExponent_left_eq, netExponent] <;> rfl

theorem skew_weighted_eq {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ) :
    weighted s i j w = SkewCone.weighted s i j w := by
  funext k
  simp only [weighted, SkewCone.weighted, skew_point_eq]

theorem skew_surplus_eq (c d p R : ℝ) :
    surplus c d p R = SkewNormalization.surplus c d R p := rfl

theorem common_skew_value (rho : ℝ) (x : Fin 6 → ℝ) :
    commonValue rho x - SkewNormalization.skew (x 0) (x 1) (x 3) (x 2) =
      SkewCone.value rho x := rfl

theorem common_skew_weighted_bound {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s, 0 ≤ w t)
    (hi : ∀ t∈s, 0 < i t) (hj : ∀ t∈s, 0 < j t)
    (rho : ℝ) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50)
    (hs : 0 ≤ surplus (weighted s i j w 0) (weighted s i j w 1)
      (weighted s i j w 2) (weighted s i j w 3)) :
    commonValue rho (weighted s i j w) -
      SkewNormalization.skew (weighted s i j w 0) (weighted s i j w 1)
        (weighted s i j w 3) (weighted s i j w 2) ≤
      (2/5:ℝ)*weighted s i j w 0 := by
  rw [common_skew_value, skew_weighted_eq]
  rw [skew_surplus_eq, skew_weighted_eq] at hs
  exact SkewCone.weighted_full_range s i j w hw hi hj rho hr hrhi hs

theorem actual_skew_vector_bound (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D)
    (Z rho : ℝ) (hZ : 1 < Z) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50)
    (hs : 0 ≤ surplus (actualVector reflected C D Z 0) (actualVector reflected C D Z 1)
      (actualVector reflected C D Z 2) (actualVector reflected C D Z 3)) :
    commonValue rho (actualVector reflected C D Z) -
      SkewNormalization.skew (actualVector reflected C D Z 0)
        (actualVector reflected C D Z 1) (actualVector reflected C D Z 3)
        (actualVector reflected C D Z 2) ≤
      (2/5:ℝ)*actualVector reflected C D Z 0 := by
  have hv := actualVector_eq_weighted reflected C D hC hD heq Z
  rw [hv] at hs ⊢
  apply common_skew_weighted_bound _ _ _ _ _ _ _ rho hr hrhi hs
  · intro P _
    exact primeWeight_nonnegative C D hC Z hZ P
  · intro P _
    cases reflected
    · exact leftExponent_pos _ _ P
    · exact rightExponent_pos _ _ P
  · intro P _
    cases reflected
    · exact rightExponent_pos _ _ P
    · exact leftExponent_pos _ _ P

theorem actual_first_common_skew_saving (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z rho delta : ℝ) (hZ : 1 < Z) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50)
    (hs : 0 ≤ TargetHigh830.labelSurplus reflected l Z) :
    let c := TargetHigh830.labelC reflected l Z
    let d := TargetHigh830.labelD reflected l Z
    let p := TargetHigh830.labelP l Z
    let R := TargetHigh830.labelR l Z
    let E := TargetHigh830.labelE l Z
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let R0 := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    ValuationGain.firstCommon rho delta c d R E Lc R0-surplus c d p R-
      SkewNormalization.skew c d R p ≤ -(delta-2/5)*c-E := by
  have hvs : 0 ≤ surplus (actualVector reflected l.1.1 l.1.2 Z 0)
      (actualVector reflected l.1.1 l.1.2 Z 1)
      (actualVector reflected l.1.1 l.1.2 Z 2)
      (actualVector reflected l.1.1 l.1.2 Z 3) := by
    simpa [surplus, actualVector, TargetHigh830.labelSurplus,
      TargetHigh830.labelC,TargetHigh830.labelD,TargetHigh830.labelP,
      TargetHigh830.labelR] using hs
  have hh := actual_skew_vector_bound reflected l.1.1 l.1.2 hC hD heq Z rho hZ hr hrhi hvs
  dsimp [commonValue, actualVector, firstSourceNumerator, ValuationGain.firstCommon,
    TargetHigh830.labelC, TargetHigh830.labelD, TargetHigh830.labelP,
    TargetHigh830.labelR, TargetHigh830.labelE] at hh ⊢
  linarith only [hh]

end
end OAI.SevenEighths.Target830.Source.Valuation

namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic LocalMoment CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentFirstCanonicalFamily Cycle63InitialMass CenteredMomentCommonSupport
open Cycle63HighGeometry Cycle63Moment
open CenteredMomentRankinRadical CenteredMomentFirstSourceReduction
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
local notation "O" => HeckeFamily.O

def labelSkew (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) : ℝ :=
  SkewNormalization.skew (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelP l Z)

theorem actual_label_common_skew (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z delta : ℝ) (hZ : 1 < Z) (hd : 31/50 ≤ delta) (hdhi : delta ≤ 3/4)
    (hs : 0 ≤ labelSurplus reflected l Z) :
    labelFirstCommon reflected l Z delta-labelSurplus reflected l Z-labelSkew reflected l Z ≤
      -(delta-2/5)*labelC reflected l Z := by
  have hr := Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith) hdhi
  have hh := Target830.Source.Valuation.actual_first_common_skew_saving reflected l
    hC hD heq Z (Target830.rho delta) delta hZ hr.1 hr.2 hs
  obtain ⟨_,hE,_,_,_,_,_⟩ := actual_first_gates (!reflected) l hC hD Z hZ
  dsimp only at hh hE
  change 0 ≤ labelE l Z at hE
  have hh' : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z-
      labelSkew reflected l Z ≤ -(delta-2/5)*labelC reflected l Z-labelE l Z := by
    simpa [labelFirstCommon, labelSurplus, labelSkew, Target830.Source.Valuation.surplus,
      labelC, labelD, labelR, labelP, Target830.Source.Valuation.rho_eq_local] using hh
  linarith only [hh',hE]

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- No scalar surplus premise remains for the actual geometry source. -/
theorem actual_geometry_label_common_skew
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0 < K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (reflected : Bool) (delta : ℝ) (hZ : 1 < Z)
    (hd : 31/50 ≤ delta) (hdhi : delta ≤ 3/4) :
    let l := geometryFirstLabel s R seed K Z xi hK bin j
    labelFirstCommon reflected l Z delta-labelSurplus reflected l Z-labelSkew reflected l Z ≤
      -(delta-2/5)*labelC reflected l Z := by
  have hs : 0 ≤ labelSurplus reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z := by
    rw [geometry_label_surplus_eq]
    exact Target830.Source.actual_surplus_nonneg s R seed K Z xi hZ j.1.val
  exact actual_label_common_skew reflected _
    (geometryFirstSource s R seed K Z xi hK bin j.1).hC
    (geometryFirstSource s R seed K Z xi hK bin j.1).hD
    (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport Z delta hZ hd hdhi hs

end
end OAI.SevenEighths.TargetHigh830

