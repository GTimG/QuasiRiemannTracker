/- Copyright (c) 2026 Sil. Apache-2.0.
Actual numerical first-band geometry for unit roots. It discharges
BandGeometry by the checked cutoff theorem; only the named analytical
RawSideBounds supply remains conditional.
-/
import Candidate.SilPrior.FourthPower.RepairedFirstRawRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedFirstRawGeometry
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource
open CenteredMomentFirstSectorLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedFirstPhysicalBudget MixedFirstCutoffs MixedFirstActualBandGeometry
open RepairedFirstRawRetained
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι]

def frequencyCap (ξ κ : ℝ) : ℝ := tailExponent (sourceExponent 8) ξ κ+ξ/2

theorem frequencyCap_nonneg (ξ κ : ℝ) (hξ : 0 ≤ ξ) (hκ : 0 ≤ κ) : 0 ≤ frequencyCap ξ κ := by
  unfold frequencyCap tailExponent sourceExponent secondExponent childExponent
  linarith

set_option maxHeartbeats 1000000 in
theorem uniform_unit_retained_of_raw_sides
    (N J : ℕ) (cRad ξ κ εmass : ℝ) (hcRad : 1 ≤ cRad)
    (hξ : 0 < ξ) (hκ : 0 < κ) (hεmass : 0 < εmass) :
    ∃ Cret : ℝ, 0 ≤ Cret ∧ ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ s : Source ι (1/4) (9/4), Fintype.card ι ≤ N → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) →
    ∀ (η : Character) (A loss : ℝ),0 ≤ A →
      RetainedRawSides s (by norm_num) η (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
      ‖retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 0 (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) ballProfile (cRad*Z) (sourceVolume s) Z ξ‖/sourceVolume s ≤
      Cret*64*fixedPresentationCost*((η.modulus.absNorm:ℝ)*cRad)*(windowMass J 0)^2*A*Z^(1+loss+εmass) := by
  obtain ⟨Cret,hCret,hret⟩ := uniform_retained_of_raw_sides (ι:=ι) (a:=1/4) (b:=9/4)
    ballProfile J 8 (frequencyCap ξ κ) 8 εmass (by norm_num)
    (frequencyCap_nonneg ξ κ hξ.le hκ.le) (by norm_num) hεmass (by norm_num)
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
    hK (Real.rpow_pos_of_pos hz _) hsource le_rfl hpool hA hband hsides
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

end
end Candidate.SilPrior.FourthPower.RepairedFirstRawGeometry
