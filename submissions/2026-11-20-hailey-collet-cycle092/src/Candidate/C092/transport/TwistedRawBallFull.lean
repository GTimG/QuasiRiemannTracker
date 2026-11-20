/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Whole first ball from genuinely colored balanced raw-side supply and proved first remainders. -/
import Candidate.C092.transport.TwistedRawBallCost
import Candidate.C092.transport.FirstColoredZeroTailFullBall
import Submissions.sil_density_split_20261026.CubeFree.FP.RepairedFirstFullBall
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectorLocalization CenteredMomentFirstLocalization
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.TwistedRawSource
open RepairedFirstFullBall
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedFirstPhysicalBudget MixedFirstSeededSource RestoredFirstRemainders
open MixedFirstCutoffs MixedFirstActualBandGeometry
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqFullBall {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι]

set_option maxHeartbeats 1000000 in
/-- Summed (balanced) form of FP `RepairedFirstRawGeometry.uniform_unit_retained_of_raw_sides`:
the actual band geometry discharged, the contract `SummedRetainedRawSides`
(`uniform_retained_of_summed_raw_sides`; no artificial-divisor mass). -/
theorem uniform_unit_retained_of_summed_raw_sides
    (N J : ℕ) (cRad ξ κ εmass : ℝ) (hcRad : 1 ≤ cRad)
    (hξ : 0 < ξ) (hκ : 0 < κ) (hεmass : 0 < εmass) :
    ∃ Cret : ℝ, 0 ≤ Cret ∧ ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ s : Source ι (1/4) (9/4), ∀ω₁ ω₂ : Id→ℂ, Fintype.card ι ≤ N → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) →
    ∀ (η : Character) (A loss : ℝ),0 ≤ A →
      SummedRetainedRawSides s (by norm_num) ω₁ ω₂ η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖CenteredMomentFirstSectorLocalization.retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 0 (sourceColumns s)
        (sourceColumn s (by norm_num) ω₁ ω₂ 1) ballProfile (cRad*Z) (sourceVolume s) Z ξ‖/sourceVolume s ≤
      Cret*64*fixedPresentationCost*((η.modulus.absNorm:ℝ)*cRad)*(windowMass J 0)^2*A*Z^(1+loss+εmass) := by
  obtain ⟨Cret,hCret,hret⟩ := uniform_retained_of_summed_raw_sides (ι:=ι) (a:=1/4) (b:=9/4)
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
  intro s ω₁ ω₂ hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hsource η A loss hA hsides
  obtain ⟨_,_,hb⟩ := hg.2 ι (1/4) s (by norm_num) ω₁ ω₂ hn hL hX₁ hX₂ hY₁ hY₂ hP
    (cRad*Z) 1 hK (by norm_num) hKcap hKinv hOne (by simpa only [inv_one] using hOne)
  have hband := hb 1 (Z^(8:ℝ))
  have he := hr.2 s (by norm_num) ω₁ ω₂ hunit η 0 (cRad*Z) (Z^(8:ℝ)) ξ κ
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

theorem source_weight_mask (s : Source ι (1/4) (9/4)) (ω₁ ω₂ : Id→ℂ)
    (η : Character) (A z : O) (t : ℝ) (I : Id) :
    sourceColumn s (by norm_num) ω₁ ω₂ 1 I * rowWeight η (fixedBadMask*idealGenerator s.R) A z t I =
      sourceColumn s (by norm_num) ω₁ ω₂ 1 I * rowWeight η fixedBadMask A z t I := by
  by_cases hc : sourceColumn s (by norm_num) ω₁ ω₂ 1 I = 0
  · simp only [hc,zero_mul]
  · have hcop := (source_nonzero_masks s (by norm_num) ω₁ ω₂ 1 I hc).1
    rw [← CenteredMomentSourceRectangleMask.rowWeight_ideal_mask η fixedBadMask A z t
      (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) s.R I]
    rw [if_pos hcop,one_mul]

theorem full_mask_identity (s : Source ι (1/4) (9/4)) (ω₁ ω₂ : Id→ℂ) (η : Character) (K : ℝ) :
    finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s) (sourceColumn s (by norm_num) ω₁ ω₂ 1) ballProfile K =
      finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 0 (sourceColumns s)
        (sourceColumn s (by norm_num) ω₁ ω₂ 1) ballProfile K := by
  have hrow (z : O) : (∑I∈sourceColumns s,
      sourceColumn s (by norm_num) ω₁ ω₂ 1 I*rowWeight η fixedBadMask 1 z 0 I) =
      ∑I∈sourceColumns s, sourceColumn s (by norm_num) ω₁ ω₂ 1 I*
        rowWeight η (fixedBadMask*idealGenerator s.R) 1 z 0 I := by
    apply Finset.sum_congr rfl
    intro I hI
    exact (source_weight_mask s ω₁ ω₂ η 1 z 0 I).symm
  unfold finiteHeckeEnergy
  simp_rw [hrow]

theorem original_first_split (s : Source ι (1/4) (9/4)) (ω₁ ω₂ : Id→ℂ)
    (η : Character) (m A : O) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (tp K Z ξ : ℝ) (Ψ : 𝓢(ℝ,ℂ)) (hK : 0<K) :
    finiteHeckeEnergy η m A tp (sourceColumns s) (sourceColumn s (by norm_num) ω₁ ω₂ 1) Ψ K =
      zeroEnergy η m A tp (sourceColumns s) (sourceColumn s (by norm_num) ω₁ ω₂ 1) Ψ K+
        CenteredMomentFirstSectorLocalization.retainedEnergy η m A tp (sourceColumns s)
          (sourceColumn s (by norm_num) ω₁ ω₂ 1) Ψ K (sourceVolume s) Z ξ+
        CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
          (sourceColumn s (by norm_num) ω₁ ω₂ 1) Ψ K (sourceVolume s) Z ξ :=
  CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized η m A tp hmLam hm2
    (sourceColumns s) (sourceColumn s (by norm_num) ω₁ ω₂ 1) Ψ K (sourceVolume s) Z ξ hK

set_option maxHeartbeats 1300000 in
/-- Conditional mechanism only. All premises other than the NAMED raw
side supply are visible source/profile/numerical bounds. The amplitude
A is linear throughout; actual application chooses it as the original
quadratic profile control times its height factor. -/
theorem fullBallCost_of_raw_sides (N J : ℕ) (cRad Cp ξ κ εmass εout : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0 < Cp) (hξ : 0 < ξ) (hκ : 0 < κ)
    (hεmass : 0 < εmass) (hεout : 0 < εout) :
    ∀η : Character,∃Cfull : ℝ,0 < Cfull ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(η₁ η₂ : Character),∀s : Source ι (1/4) (9/4),Fintype.card ι ≤ N → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) → sourceVolume s ≤ Z^(8:ℝ) →
    ∀A loss : ℝ,0 ≤ A → (profileCap s)^2 ≤ Cp*A → loss+εmass ≤ εout →
      SummedRetainedRawSides s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1) ballProfile (cRad*Z)‖/sourceVolume s ≤ Cfull*A*Z^(1+εout) := by
  obtain ⟨Cret,hCret,hret⟩ := uniform_unit_retained_of_summed_raw_sides (ι:=ι) N J cRad ξ κ εmass hcRad hξ hκ hεmass
  obtain ⟨Crem,hCrem,hrem⟩ := FirstColoredZeroTail.uniform_unit_zero_tail.{u} N ballProfile cRad Cp εout ξ hcRad hCp hεout hξ
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
  intro η₁ η₂ s hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol A loss hA hprofile hloss hsides
  let m := fixedBadMask*idealGenerator s.R
  let zero := zeroEnergy η m 1 0 (sourceColumns s) (sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1) ballProfile (cRad*Z)
  let kept := CenteredMomentFirstSectorLocalization.retainedEnergy η m 1 0 (sourceColumns s) (sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)
    ballProfile (cRad*Z) (sourceVolume s) Z ξ
  let tail := CenteredMomentFirstSectorLocalization.discardedEnergy η m 1 0 (sourceColumns s) (sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)
    ballProfile (cRad*Z) (sourceVolume s) Z ξ
  have hremainders := hremZ.2 ι s hn hunit A hA
    hprofile hpool hnorm hvol η₁ η₂ η m 1 0
  have hretained := hretZ.2 s (idealCoeff η₁) (idealCoeff η₂) hn hunit hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm η A loss hA hsides
  have hkept : ‖kept‖/sourceVolume s ≤ Kret*A*Z^(1+εout) := by
    apply hretained.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      (mul_nonneg hKret hA)
  have hmLam : goodLambda∣m := (dvd_mul_right goodLambda (2:O)).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣m := (dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right _ _)
  have hsplit := original_first_split s (idealCoeff η₁) (idealCoeff η₂) η m 1 hmLam hm2 0 (cRad*Z) Z ξ ballProfile hK
  have hid : finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1) ballProfile (cRad*Z)=zero+kept+tail :=
    (full_mask_identity s (idealCoeff η₁) (idealCoeff η₂) η (cRad*Z)).trans hsplit
  rw [hid]
  have htriangle := (norm_add_le (zero+kept) tail).trans
    (add_le_add (norm_add_le zero kept) (le_refl ‖tail‖))
  calc
    _ ≤ (‖zero‖+‖kept‖+‖tail‖)/sourceVolume s :=
      div_le_div_of_nonneg_right htriangle (sourceVolume_pos s).le
    _ = (‖zero‖/sourceVolume s+‖tail‖/sourceVolume s)+‖kept‖/sourceVolume s := by ring
    _ ≤ Crem*A*Z^(1+εout)+Kret*A*Z^(1+εout) := add_le_add hremainders hkept
    _ = _ := by ring

#print axioms uniform_unit_retained_of_summed_raw_sides
#print axioms full_mask_identity
#print axioms original_first_split
#print axioms fullBallCost_of_raw_sides
end
end QRH.Cycle092.TwistedRawBall
