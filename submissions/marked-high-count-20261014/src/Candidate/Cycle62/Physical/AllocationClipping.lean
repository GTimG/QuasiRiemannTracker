import Candidate.Cycle62.Physical.ClippedProjector
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell

namespace Cycle62.Physical

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

/-- This is the actual change in the two-plain normalizer, including negative
raw lengths. -/
theorem clipping_ratio_log (Z : ℝ) (X : Fin 2 → ℝ) (hZ : 1 < Z)
    (hX : ∀ j, 0 < X j) :
    Real.logb Z ((clippedScale (X 0)*clippedScale (X 1))/(X 0*X 1)) =
      negativeTotal (fun j => Real.logb Z (X j)) := by
  have hc (j : Fin 2) : 0 < clippedScale (X j) :=
    zero_lt_one.trans_le (clippedScale_ge_one _)
  rw [Real.logb_div (mul_pos (hc 0) (hc 1)).ne' (mul_pos (hX 0) (hX 1)).ne',
    Real.logb_mul (hc 0).ne' (hc 1).ne',
    Real.logb_mul (hX 0).ne' (hX 1).ne',
    logb_clipped_scale Z _ hZ (hX 0), logb_clipped_scale Z _ hZ (hX 1)]
  simp only [negativeTotal, Fin.sum_univ_two]
  linarith [max_positive_sub (Real.logb Z (X 0)),
    max_positive_sub (Real.logb Z (X 1))]

theorem clipping_ratio_rpow (Z : ℝ) (X : Fin 2 → ℝ) (hZ : 1 < Z)
    (hX : ∀ j, 0 < X j) :
    Z^(negativeTotal (fun j => Real.logb Z (X j))) =
      (clippedScale (X 0)*clippedScale (X 1))/(X 0*X 1) := by
  rw [← clipping_ratio_log Z X hZ hX]
  exact Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (div_pos (mul_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _))) (mul_pos (hX 0) (hX 1)))

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

/-- The scalar is the literal change in the actual normalizer; no new
coprimality condition is attached to either plain quotient. -/
theorem actual_clipped_scalar_squared (Z : ℝ) (hZ : 1 < Z)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) (hP : ∀ i, 0 < P i) (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) :
    Z^(-clippedReduction (Real.logb Z (formalReductionFactor D a P))
        (fun j => Real.logb Z (X j)) (actualPlainReduction Z D a)+
      negativeTotal (fun j => Real.logb Z (X j))) =
      ((clippedScale (postPlainScale D a X 0)*clippedScale (postPlainScale D a X 1))/
        (postPlainScale D a X 0*postPlainScale D a X 1))/formalReductionFactor D a P := by
  have hF : 0 < formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _ => hP i))
  have hz : 0 < Z := zero_lt_one.trans hZ
  have he : -clippedReduction (Real.logb Z (formalReductionFactor D a P))
      (fun j => Real.logb Z (X j)) (actualPlainReduction Z D a)+
      negativeTotal (fun j => Real.logb Z (X j)) =
      -Real.logb Z (formalReductionFactor D a P)+
        negativeTotal (fun j => Real.logb Z (postPlainScale D a X j)) := by
    simp only [postPlainScale_log Z D a X hX, clippedReduction]
    ring
  rw [he, Real.rpow_add hz, Real.rpow_neg hz.le,
    Real.rpow_logb hz hZ.ne' hF,
    clipping_ratio_rpow Z _ hZ (postPlainScale_pos D a X hX)]
  ring

end
end Cycle62.Physical

#print axioms Cycle62.Physical.actual_post_clipping_bound
#print axioms Cycle62.Physical.actual_clipped_scalar_squared
