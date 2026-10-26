import Candidate.Uneven.SkewCone
import Candidate.Target830.High.BalancedMass
import Candidate.Uneven.Columns
import Candidate.Uneven.ActualCommon
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

/- Original module: Candidate.Uneven.SkewSize. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
namespace SkewNormalization
noncomputable section

theorem clip_abs_le {s r R : ℝ} (hs : 0 ≤ s) (hr : |r| ≤ R) :
    |clip s r| ≤ R := by
  obtain ⟨hr0,hr1⟩ := abs_le.mp hr
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  unfold clip
  simp only [max_def,min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem skew_abs_le_tenth {c d r p B : ℝ}
    (hc : 0 ≤ c ∧ c ≤ B) (hd : 0 ≤ d ∧ d ≤ B)
    (hs : 0 ≤ surplus c d r p) : |skew c d r p| ≤ B/10 := by
  apply clip_abs_le hs
  rw [abs_le]
  constructor <;> linarith [hc.1,hc.2,hd.1,hd.2]

end
end SkewNormalization
end

/- Original module: Candidate.Uneven.HighMass. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open CenteredMomentFirstPhysicalSource CenteredMomentExceptionalAmplitudePair CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentCommonHeightEnvelope
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

def unevenGeometrySide (reflected : Bool) (A : ℝ) (v : Fin 5→ℝ) : ℝ :=
  if reflected then Target830.Source.Uneven.unevenRight A v
  else Target830.Source.Uneven.unevenLeft A v

def unevenFirstHighMass (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) : ℝ :=
  geometryFirstHighMass reflected s R seed W D Z xi e hK bin j*
    Z^(-Target830.Source.Uneven.allocation reflected (geometryExponents s R seed (Z^D) Z xi j.1.val))

theorem uneven_first_high_mass_nonneg (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) (hZ : 0 ≤ Z) :
    0 ≤ unevenFirstHighMass reflected s R seed W D Z xi e hK bin j := by
  exact mul_nonneg (geometry_first_high_mass_nonneg reflected s R seed W D Z xi e hK bin j)
    (Real.rpow_nonneg hZ _)

theorem uneven_first_high_mass_formula (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (hZ : 0<Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) :
    unevenFirstHighMass reflected s R seed W D Z xi e hK bin j=
    ‖Target830.Source.Uneven.unevenColumnScalar reflected s R seed (Z^D) Z xi D
      (Real.logb Z (volume s.toData)) hK bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z xi q)) j‖^2*
      ((geometryColumnIdeal reflected s R seed (Z^D) Z xi hK bin j).absNorm:ℝ)^(e-1) := by
  rw [Target830.Source.Uneven.unevenColumnScalar_norm_sq reflected s R seed (Z^D) Z xi D
    (Real.logb Z (volume s.toData)) hK bin
    (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z xi q)) j hZ]
  unfold unevenFirstHighMass geometryFirstHighMass
  ring

/-- The new denominator cancels the actual surplus label by label. The
external D-compensator and original support constant are unchanged. -/
theorem actual_uneven_uniform_high_mass (reflected : Bool) (N : ℕ) (lo ap : ℝ)
    (hlo : 0<lo) (hap : 0<ap) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi B e : ℝ) (hZ : 1<Z) (hK : 0<Z^D)
    (he : 0 ≤ e) (hcard : Fintype.card alpha ≤ N) (hlower : lo ≤ s.lower)
    (hs : Squarefree seed) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B)
    (hs1 : ∀x,s.W₁ x≠0 → ap ≤ x) (hs2 : ∀x,s.W₂ x≠0 → ap ≤ x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) :
    unevenFirstHighMass reflected s R seed W D Z xi e hK bin j ≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*e)/
        Z^(unevenGeometrySide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^D) Z xi j.1.val)) := by
  have hp : 0<Z := zero_lt_one.trans hZ
  have hm:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z xi B e
    hZ hK he hcard hlower hs hz1 hz2 hsource hs1 hs2 bin j
  have hh:=mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg hp.le (-Target830.Source.Uneven.allocation reflected (geometryExponents s R seed (Z^D) Z xi j.1.val)))
  unfold unevenFirstHighMass
  refine hh.trans_eq ?_
  have hid : unevenGeometrySide reflected (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^D) Z xi j.1.val)=
      geometryHighSide reflected (Real.logb Z (volume s.toData))
        (geometryExponents s R seed (Z^D) Z xi j.1.val)+
      Target830.Source.Uneven.allocation reflected (geometryExponents s R seed (Z^D) Z xi j.1.val) := by
    cases reflected
    · exact Target830.Source.Uneven.left_eq_old _ _
    · exact Target830.Source.Uneven.right_eq_old _ _
  rw [hid,Real.rpow_add hp]
  simp only [div_eq_mul_inv,mul_inv,Real.rpow_neg hp.le]
  ring


theorem uneven_geometry_side_eq (reflected : Bool) (A : ℝ) (v : Fin 5→ℝ) :
    unevenGeometrySide reflected A v=balancedGeometrySide reflected A v+
      (if reflected then -Target830.Source.Uneven.skew v else Target830.Source.Uneven.skew v) := by
  cases reflected <;> simp [unevenGeometrySide,balancedGeometrySide,
    Target830.Source.Uneven.unevenLeft,Target830.Source.Uneven.unevenRight,sub_eq_add_neg]

theorem uneven_geometry_side_box (reflected : Bool) (A B : ℝ) (v : Fin 5→ℝ)
    (hB : 0 ≤ B) (hA : |A| ≤ B) (hv : ∀j,0 ≤ v j ∧ v j ≤ B)
    (hs : 0 ≤ Target830.Source.surplus v) :
    |unevenGeometrySide reflected A v| ≤ 6*B := by
  have hbase := balanced_geometry_side_box reflected A B v hB hA hv
  have hsk : |Target830.Source.Uneven.skew v| ≤ B/10 :=
    SkewNormalization.skew_abs_le_tenth (hv 0) (hv 1) hs
  rw [uneven_geometry_side_eq]
  calc
    _ ≤ |balancedGeometrySide reflected A v|+
        |if reflected then -Target830.Source.Uneven.skew v else Target830.Source.Uneven.skew v| := abs_add_le _ _
    _ ≤ 5*B+B/10 := add_le_add hbase (by cases reflected <;> simpa using hsk)
    _ ≤ 6*B := by linarith

theorem geometry_label_skew_eq (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ)
    (hK : 0 < K) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin)) (reflected : Bool) :
    labelSkew reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z=
      (if reflected then -Target830.Source.Uneven.skew (geometryExponents s R seed K Z xi j.1.val)
       else Target830.Source.Uneven.skew (geometryExponents s R seed K Z xi j.1.val)) := by
  have hs := Target830.Source.actual_surplus_nonneg s R seed K Z xi hZ j.1.val
  let v := geometryExponents s R seed K Z xi j.1.val
  cases reflected
  · rfl
  · change SkewNormalization.skew (v 1) (v 0) (v 3) (v 2)=
      -SkewNormalization.skew (v 0) (v 1) (v 3) (v 2)
    exact SkewNormalization.skew_reflect _ _ _ _ hs

theorem uneven_geometry_side_label (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ)
    (hK : 0 < K) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin)) (reflected : Bool) (A : ℝ) :
    unevenGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)=
      balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)+
        labelSkew reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z := by
  rw [uneven_geometry_side_eq,geometry_label_skew_eq s R seed K Z xi hK hZ bin j reflected]

end OAI.SevenEighths.TargetHigh830
end
