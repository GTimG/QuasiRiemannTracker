/- Copyright (c) 2026 Sil. Apache-2.0.
EXPLICIT mechanism: raw first-side supply -> actual full ball cost.
First numerical geometry and first zero/tail are supplied internally.
The summed raw-side contract First.SummedRetainedRawSides is the only
analytical premise.
Modified by Sil (2026-10-26): the raw-side premise is the balanced summed Seam 0 First.SummedRetainedRawSides; FP RepairedFirstRawGeometry.uniform_unit_retained_of_raw_sides (on the replaced per-divisor RepairedFirstRawRetained) is restated here as uniform_unit_retained_of_summed_raw_sides through First.uniform_retained_of_summed_raw_sides (no artificial-divisor mass; same right-hand side); the import of RepairedFirstRawGeometry is replaced by First.RawSidesRetained.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.First.RawSidesRetained
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstActualBandGeometry
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RestoredFirstRemainders
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstSeededSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedFirstFullBall
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectorLocalization CenteredMomentFirstLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedFirstPhysicalBudget MixedFirstSeededSource RestoredFirstRemainders
open MixedFirstCutoffs MixedFirstActualBandGeometry
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqFullBall {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι]

/-- FP `RepairedFirstRawGeometry.frequencyCap`. -/
def frequencyCap (ξ κ : ℝ) : ℝ := tailExponent (sourceExponent 8) ξ κ+ξ/2

theorem frequencyCap_nonneg (ξ κ : ℝ) (hξ : 0 ≤ ξ) (hκ : 0 ≤ κ) : 0 ≤ frequencyCap ξ κ := by
  unfold frequencyCap tailExponent sourceExponent secondExponent childExponent
  linarith

set_option maxHeartbeats 1000000 in
/-- Summed (balanced) form of FP `RepairedFirstRawGeometry.uniform_unit_retained_of_raw_sides`:
the actual band geometry discharged, the contract `First.SummedRetainedRawSides`
(`First.uniform_retained_of_summed_raw_sides`; no artificial-divisor mass). -/
theorem uniform_unit_retained_of_summed_raw_sides
    (N J : ℕ) (cRad ξ κ εmass : ℝ) (hcRad : 1 ≤ cRad)
    (hξ : 0 < ξ) (hκ : 0 < κ) (hεmass : 0 < εmass) :
    ∃ Cret : ℝ, 0 ≤ Cret ∧ ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ s : Source ι (1/4) (9/4), Fintype.card ι ≤ N → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) →
    ∀ (η : Character) (A loss : ℝ),0 ≤ A →
      First.SummedRetainedRawSides s (by norm_num) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖CenteredMomentFirstSectorLocalization.retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z) (sourceVolume s) Z ξ‖/sourceVolume s ≤
      Cret*64*fixedPresentationCost*((η.modulus.absNorm:ℝ)*cRad)*(windowMass J 0)^2*A*Z^(1+loss+εmass) := by
  obtain ⟨Cret,hCret,hret⟩ := First.uniform_retained_of_summed_raw_sides (ι:=ι) (a:=1/4) (b:=9/4)
    ballProfile J 8 (frequencyCap ξ κ) εmass (by norm_num)
    (frequencyCap_nonneg ξ κ hξ.le hκ.le) hεmass
  have hgeometry := uniform_actual_band_geometry.{u} N (9/4) 8 ξ ξ κ (by norm_num) (by norm_num) hξ.le hξ hκ
  refine ⟨Cret,hCret,?_⟩
  filter_upwards [hret,hgeometry,eventually_ge_atTop cRad,eventually_ge_atTop (2:ℝ)] with Z hr hg hcZ hZ2
  have hZ := hr.1
  have hz := zero_lt_one.trans hZ
  have hK : 0 < cRad*Z := mul_pos (zero_lt_one.trans_le hcRad) hz
  have hKcap : cRad*Z ≤ Z^(8:ℝ) := by
    calc
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hcZ hz.le
      _ = Z^(2:ℝ) := by rw [Real.rpow_two];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hKinv : (cRad*Z)⁻¹ ≤ Z^(8:ℝ) :=
    (inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le hcRad hZ.le)).trans
      (Real.one_le_rpow hZ.le (by norm_num))
  have hOne : (1:ℝ) ≤ Z^(8:ℝ) := Real.one_le_rpow hZ.le (by norm_num)
  refine ⟨hZ,?_⟩
  intro s hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hsource η A loss hA hsides
  obtain ⟨_,_,hb⟩ := hg.2 ι (1/4) s (by norm_num) hn hL hX₁ hX₂ hY₁ hY₂ hP
    (cRad*Z) 1 hK (by norm_num) hKcap hKinv hOne (by simpa only [inv_one] using hOne)
  have hband := hb 1 (Z^(8:ℝ))
  have he := hr.2 s (by norm_num) hunit η 0 (cRad*Z) (Z^(8:ℝ)) ξ κ
    (secondCutoff (sourceExponent 8) Z) (tailExponent (sourceExponent 8) ξ κ) A loss
    hK (Real.rpow_pos_of_pos hz _) hsource le_rfl hA hband hsides
  have hpower : Z*Z^(loss+εmass)=Z^(1+loss+εmass) := by
    calc
      _=Z^(1:ℝ)*Z^(loss+εmass) := by rw [Real.rpow_one]
      _=Z^(1+(loss+εmass)) := (Real.rpow_add hz 1 (loss+εmass)).symm
      _=_ := by congr 1; ring
  apply he.trans_eq
  rw [show (4/(1/4:ℝ)^2)=64 by norm_num]
  calc
    _=(Cret*64*fixedPresentationCost*((η.modulus.absNorm:ℝ)*cRad)*(windowMass J 0)^2*A)*
        (Z*Z^(loss+εmass)) := by ring
    _=_ := by rw [hpower]

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
      First.SummedRetainedRawSides s (by norm_num) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z)‖/sourceVolume s ≤ Cfull*A*Z^(1+εout) := by
  obtain ⟨Cret,hCret,hret⟩ := uniform_unit_retained_of_summed_raw_sides (ι:=ι) N J cRad ξ κ εmass hcRad hξ hκ hεmass
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
end Qrh.MarkedAnchor.Ordinary.FP.RepairedFirstFullBall

