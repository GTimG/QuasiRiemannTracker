/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.InitialMomentInlet

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice
local notation "O" => HeckeFamily.O

/-- Removing clipping increases the whole normalized positive norm. This exact
normalization comparison eliminates the row-dependent clipping profile without
putting arithmetic data into a seminorm. Quotient scales need only be positive. -/
theorem retained_positive_le_original {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i, 0 < P i) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂‖^2 ≤
      ‖positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂‖^2 := by
  have hid := retained_rectangle_raw_energy η m A z W₁ W₂ pool β P hP t X₁ X₂
    (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)
  have hclip : X₁*X₂ ≤ clippedScale X₁*clippedScale X₂ :=
    mul_le_mul (le_max_right 1 X₁) (le_max_right 1 X₂) hX₂.le
      (zero_lt_one.trans_le (clippedScale_ge_one X₁)).le
  have hratio : 1 ≤ clippedScale X₁*clippedScale X₂/(X₁*X₂) :=
    (one_le_div (mul_pos hX₁ hX₂)).mpr hclip
  change ‖positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂‖^2 = _ at hid
  rw [hid]
  exact le_mul_of_one_le_left (sq_nonneg _) hratio

/-- The un-clipped positive norm is exactly the common-profile natural product,
with the original whole normalization and all relative-slot height phases. -/
theorem natural_punctured_product_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R ≠ 0)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i, 0 < P i) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ pool β P t X₁ X₂‖ =
      ‖polynomial (excluded F.character R) false
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t) X₁ 0 0 *
      polynomial (excluded F.character R) false
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) X₂ 0 0 *
      ∏ i, naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)‖ := by
  have h := congrArg (fun x : ℂ => ‖x‖) (original_positive_normalized F R hR
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool β P hP t X₁ X₂ hX₁ hX₂)
  simpa only [norm_mul,positive_height_phase_norm _ _ hX₁,
    positive_height_phase_norm _ _ hX₂,one_mul] using h

/-- The actual clipped physical row is dominated by the common-profile
punctured natural product, retaining both plain scales and the complete slots. -/
theorem retained_natural_common_profile {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R ≠ 0)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i, 0 < P i) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z
      W₁ W₂ pool β P t X₁ X₂‖^2 ≤
      ‖polynomial (excluded F.character R) false
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t) X₁ 0 0 *
      polynomial (excluded F.character R) false
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) X₂ 0 0 *
      ∏ i, naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)‖^2 := by
  have h := retained_positive_le_original η (fixedBadMask*idealGenerator R) 1 z
    W₁ W₂ pool β P hP t X₁ X₂ hX₁ hX₂
  rwa [natural_punctured_product_norm F R hR W₁ W₂ a b ha hs₁ hs₂
    pool β P hP t X₁ X₂ hX₁ hX₂] at h

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.retained_positive_le_original
#print axioms OAI.SevenEighths.Record12518109Raw.natural_punctured_product_norm
#print axioms OAI.SevenEighths.Record12518109Raw.retained_natural_common_profile
