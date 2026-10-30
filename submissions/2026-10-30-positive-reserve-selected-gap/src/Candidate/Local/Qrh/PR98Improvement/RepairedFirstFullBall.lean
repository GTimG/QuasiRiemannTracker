/- Reserve-parametric adaptation by Joseph Bebel (2026). -/
/- Copyright (c) 2026 Sil. Apache-2.0.
EXPLICIT mechanism: raw first-side supply -> actual full ball cost.
First numerical geometry and first zero/tail are supplied internally.
RetainedRawSides is the only remaining analytical premise, to be
discharged by Raw/Small before this can close a source theorem.
-/
import Candidate.Local.Qrh.PR98Improvement.RepairedFirstRawGeometry
import Candidate.Local.Qrh.PR98Improvement.RestoredFirstRemainders
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstSeededSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.PR98.RepairedFirstFullBall
universe u
noncomputable section
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectorLocalization CenteredMomentFirstLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedFirstPhysicalBudget MixedFirstSeededSource Candidate.PR98.RestoredFirstRemainders
open Candidate.PR98.RepairedFirstRawRetained Candidate.PR98.RepairedFirstRawGeometry
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι]

/-- The Source.R mask is redundant by the checked original coefficient
identity. In particular this does NOT assert idealGenerator(1)=1. -/
theorem full_mask_identity (s : Source ι (1/4) (9/4)) (η : Character) (K : ℝ) :
    finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s) (sourceCoefficient s (by norm_num) 1) ballProfile K=
      finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile K := by
  have he := source_mask_energy s (by norm_num) 1 s.R (dvd_refl _)
    η 1 0 (fun _ => 1) ballProfile K
  simpa only [mul_one] using he.symm

set_option maxHeartbeats 1300000 in
/-- Conditional mechanism only. All premises other than the NAMED raw
side supply are visible source/profile/numerical bounds. The amplitude
A is linear throughout; actual application chooses it as the original
quadratic profile control times its height factor. -/
theorem fullBallCost_of_raw_sides (N J : ℕ) (cRad Cp ξ κ εmass εout : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0 < Cp) (hξ : 0 < ξ) (hκ : 0 < κ)
    (hεmass : 0 < εmass) (hεout : 0 < εout) :
    ∀η : Character,∃Cfull : ℝ,0 < Cfull ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀s : Source ι (1/4) (9/4),Fintype.card ι ≤ N → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) → sourceVolume s ≤ Z^(8:ℝ) →
    ∀A loss : ℝ,0 ≤ A → (profileCap s)^2 ≤ Cp*A → loss+εmass ≤ εout →
      RetainedRawSides s (by norm_num) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z)‖/sourceVolume s ≤ Cfull*A*Z^(1+εout) := by
  obtain ⟨Cret,hCret,hret⟩ := uniform_unit_retained_of_raw_sides (ι:=ι) N J cRad ξ κ εmass hcRad hξ hκ hεmass
  obtain ⟨Crem,hCrem,hrem⟩ := uniform_unit_zero_tail.{u} N ballProfile cRad Cp εout ξ hcRad hCp hεout hξ
  intro η
  let Kret := Cret*64*fixedPresentationCost*((η.modulus.absNorm:ℝ)*cRad)*(windowMass J 0)^2
  have hKret : 0 ≤ Kret := by
    have hf := fixedPresentationCost_pos
    have hc : 0 ≤ cRad := zero_le_one.trans hcRad
    dsimp only [Kret]
    positivity
  refine ⟨Crem+Kret,add_pos_of_pos_of_nonneg hCrem hKret,?_⟩
  filter_upwards [hret,hrem] with Z hretZ hremZ
  have hZ := hretZ.1
  have hz := zero_lt_one.trans hZ
  have hK : 0 < cRad*Z := mul_pos (zero_lt_one.trans_le hcRad) hz
  refine ⟨hZ,?_⟩
  intro s hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol A loss hA hprofile hloss hsides
  let m := fixedBadMask*idealGenerator s.R
  let zero := zeroEnergy η m 1 0 (sourceColumns s) (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z)
  let kept := CenteredMomentFirstSectorLocalization.retainedEnergy η m 1 0 (sourceColumns s) (sourceCoefficient s (by norm_num) 1)
    ballProfile (cRad*Z) (sourceVolume s) Z ξ
  let tail := CenteredMomentFirstSectorLocalization.discardedEnergy η m 1 0 (sourceColumns s) (sourceCoefficient s (by norm_num) 1)
    ballProfile (cRad*Z) (sourceVolume s) Z ξ
  have hprof' : (profileCap s)^2 ≤ Cp*(Real.sqrt A)^2 := by
    simpa only [Real.sq_sqrt hA] using hprofile
  have hremainders := hremZ.2 ι s hn hunit (Real.sqrt A) (Real.sqrt_nonneg A)
    hprof' hpool hnorm hvol η m 1 0
  simp only [Real.sq_sqrt hA] at hremainders
  have hretained := hretZ.2 s hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm η A loss hA hsides
  have hkept : ‖kept‖/sourceVolume s ≤ Kret*A*Z^(1+εout) := by
    apply hretained.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      (mul_nonneg hKret hA)
  have hmLam : goodLambda∣m := (dvd_mul_right goodLambda (2:O)).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣m := (dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right _ _)
  have hsplit := original_first_split s (by norm_num) η m 1 hmLam hm2 0 (cRad*Z) Z ξ ballProfile hK
  have hid : finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z)=zero+kept+tail :=
    (full_mask_identity s η (cRad*Z)).trans hsplit
  rw [hid]
  have htriangle := (norm_add_le (zero+kept) tail).trans
    (add_le_add (norm_add_le zero kept) (le_refl ‖tail‖))
  calc
    _ ≤ (‖zero‖+‖kept‖+‖tail‖)/sourceVolume s :=
      div_le_div_of_nonneg_right htriangle (sourceVolume_pos s).le
    _ = (‖zero‖/sourceVolume s+‖tail‖/sourceVolume s)+‖kept‖/sourceVolume s := by ring
    _ ≤ Crem*A*Z^(1+εout)+Kret*A*Z^(1+εout) := add_le_add hremainders hkept
    _ = _ := by ring

end
end Candidate.PR98.RepairedFirstFullBall

