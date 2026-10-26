import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ClippedProjector
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Physical

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentRetainedEnergy
open CenteredMomentRetainedProfile CenteredMomentActiveDivisorShell
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots
local notation "O" => ActualEisensteinCubic.O

theorem logb_clipped_scale (Z X : ℝ) (hZ : 1 < Z) (hX : 0 < X) :
    Real.logb Z (clippedScale X) = max 0 (Real.logb Z X) := by
  by_cases hx : 1 ≤ X
  · simp only [clippedScale, max_eq_right hx,
      max_eq_right (Real.logb_nonneg hZ hx)]
  · have hx1 : X ≤ 1 := le_of_lt (lt_of_not_ge hx)
    simp only [clippedScale, max_eq_left hx1, Real.logb_one,
      max_eq_left (Real.logb_nonpos hZ hX.le hx1)]

theorem max_positive_sub (x : ℝ) : max 0 x-x = max 0 (-x) := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx, max_eq_left (by linarith : -x ≤ 0)]
    ring
  · rw [max_eq_left (le_of_not_ge hx), max_eq_right (by linarith : 0 ≤ -x)]
    ring

theorem row_sum_support_scale (η : Character) (m A z : O) (W : ℝ → ℂ)
    (t X b : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b)
    (hn : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b*X := by
  have hw : ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ)/X) ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    unfold rowTwistedSum
    calc
      _ = ∑' _I : Ideal O, (0 : ℂ) := by
        apply tsum_congr
        intro I
        by_cases hI : I=0
        · subst I
          rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
        · rw [h I hI, mul_zero]
      _ = 0 := tsum_zero
  obtain ⟨I,hI,hW⟩ := hw
  have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hN.trans ((div_le_iff₀ hX).mp (hs hW))

/-- Nonzero terms, rather than a nominal scale gate, supply the clipping cap. -/
theorem supported_negative_total (Z : ℝ) (X b : Fin 2 → ℝ)
    (hZ : 1 < Z) (hX : ∀ j, 0 < X j) (hs : ∀ j, 1 ≤ b j*X j) :
    negativeTotal (fun j => Real.logb Z (X j)) ≤
      ∑ j, Real.logb Z (max 1 (b j)) := by
  have hj (j : Fin 2) : max 0 (-Real.logb Z (X j)) ≤
      Real.logb Z (max 1 (b j)) := by
    have hB : 0 < max 1 (b j) := zero_lt_one.trans_le (le_max_left _ _)
    have hm : clippedScale (X j) ≤ max 1 (b j)*X j := by
      apply max_le
      · exact (hs j).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hX j).le)
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (b j)) (hX j).le
    have hh := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hm
    rw [Real.logb_mul hB.ne' (hX j).ne', logb_clipped_scale Z _ hZ (hX j)] at hh
    linarith [max_positive_sub (Real.logb Z (X j))]
  exact Finset.sum_le_sum (fun j _ => hj j)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def postPlainScale (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  X j/(Ideal.absNorm (selectedPlain D a j) : ℝ)

theorem postPlainScale_pos (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (j : Fin 2) :
    0 < postPlainScale D a X j := by
  apply div_pos (hX j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

theorem postPlainScale_log (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (j : Fin 2) :
    Real.logb Z (postPlainScale D a X j) =
      Real.logb Z (X j)-actualPlainReduction Z D a j := by
  exact Real.logb_div (hX j).ne' (by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

theorem actual_post_support (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X : Fin 2 → ℝ) (b₁ b₂ : ℝ)
    (hX : ∀ j, 0 < X j)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hn : allocatedPositiveRow η m A z t S β P D a W₁ W₂ (X 0) (X 1) ≠ 0) :
    1 ≤ b₁*postPlainScale D a X 0 ∧ 1 ≤ b₂*postPlainScale D a X 1 := by
  unfold allocatedPositiveRow retainedPositiveRow positiveSlotRow at hn
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul hn)
  have h₁ : rowTwistedSum η m A z W₁ t (postPlainScale D a X 0) ≠ 0 := by
    rw [clipped_rowTwistedSum η m A z W₁ t _ (postPlainScale_pos D a X hX 0)]
    exact left_ne_zero_of_mul hp
  have h₂ : rowTwistedSum η m A z W₂ t (postPlainScale D a X 1) ≠ 0 := by
    rw [clipped_rowTwistedSum η m A z W₂ t _ (postPlainScale_pos D a X hX 1)]
    exact right_ne_zero_of_mul hp
  exact ⟨row_sum_support_scale η m A z W₁ t _ b₁
    (postPlainScale_pos D a X hX 0) hs₁ h₁,
    row_sum_support_scale η m A z W₂ t _ b₂
      (postPlainScale_pos D a X hX 1) hs₂ h₂⟩

theorem actual_post_clipping_bound (Z : ℝ) (hZ : 1 < Z)
    (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X b : Fin 2 → ℝ) (hX : ∀ j, 0 < X j)
    (hs₁ : Function.support W₁ ⊆ Set.Iic (b 0))
    (hs₂ : Function.support W₂ ⊆ Set.Iic (b 1))
    (hn : allocatedPositiveRow η m A z t S β P D a W₁ W₂ (X 0) (X 1) ≠ 0) :
    negativeTotal (fun j => Real.logb Z (X j)-actualPlainReduction Z D a j) ≤
      ∑ j, Real.logb Z (max 1 (b j)) := by
  have hh := actual_post_support η m A z t S β P D a W₁ W₂ X (b 0) (b 1)
    hX hs₁ hs₂ hn
  have hs : ∀ j : Fin 2, 1 ≤ b j*postPlainScale D a X j := by
    intro j
    fin_cases j
    · exact hh.1
    · exact hh.2
  simpa only [postPlainScale_log Z D a X hX] using
    supported_negative_total Z (postPlainScale D a X) b hZ
      (postPlainScale_pos D a X hX) hs

end
end Cycle63.Physical

end Record1252270103Bootstrap.PR67
