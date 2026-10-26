import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorRetained

namespace Cycle63.Physical

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O

def negativeTotal (x : Fin 2 → ℝ) : ℝ := ∑ i, max 0 (-x i)

def clippedReduction (r : ℝ) (x a : Fin 2 → ℝ) : ℝ :=
  r - (negativeTotal (fun i => x i-a i)-negativeTotal x)

theorem negative_clip_gain (x a : ℝ) (ha : 0 ≤ a) :
    0 ≤ max 0 (-(x-a))-max 0 (-x) ∧
      max 0 (-(x-a))-max 0 (-x) ≤ a := by
  have hmono : max 0 (-x) ≤ max 0 (-(x-a)) := max_le_max (le_refl _) (by linarith)
  have hupper : max 0 (-(x-a)) ≤ a+max 0 (-x) := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (-x)]
    · linarith [le_max_right (0:ℝ) (-x)]
  constructor <;> linarith

theorem clippedReduction_nonneg (r : ℝ) (x a : Fin 2 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : ∑ i, a i ≤ r) :
    0 ≤ clippedReduction r x a := by
  have hs : negativeTotal (fun i => x i-a i)-negativeTotal x ≤ ∑ i, a i := by
    rw [negativeTotal, negativeTotal, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => (negative_clip_gain (x i) (a i) (ha i)).2)
  unfold clippedReduction
  linarith

theorem clippedReduction_le_raw (r : ℝ) (x a : Fin 2 → ℝ)
    (ha : ∀ i, 0 ≤ a i) : clippedReduction r x a ≤ r := by
  have hs : 0 ≤ negativeTotal (fun i => x i-a i)-negativeTotal x := by
    rw [negativeTotal, negativeTotal, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun i _ => (negative_clip_gain (x i) (a i) (ha i)).1)
  unfold clippedReduction
  linarith

/-- The clipped exponent is attached to each positive rectangle separately. -/
theorem extraction_scalar_identity (r e : ℝ) (x a : Fin 2 → ℝ) :
    (-clippedReduction r x a+e+negativeTotal x)/2 =
      (-r+e+negativeTotal (fun i => x i-a i))/2 := by
  unfold clippedReduction
  ring

theorem extraction_scalar_rpow (Z r e : ℝ) (hZ : 0 < Z) (x a : Fin 2 → ℝ) :
    Z^(-r/2)*Z^((e+negativeTotal (fun i => x i-a i))/2) =
      Z^((-clippedReduction r x a+e+negativeTotal x)/2) := by
  rw [← Real.rpow_add hZ, extraction_scalar_identity]
  congr 1
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualPlainReduction (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  Real.logb Z (Ideal.absNorm (selectedPlain D a j) : ℝ)

theorem actual_plain_reduction_nonneg (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) :
    0 ≤ actualPlainReduction Z D a j := by
  apply Real.logb_nonneg hZ
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

/-- The actual allocation's formal reduction pays every selected plain factor;
the additional frozen-slot scales can only increase that payment. -/
theorem actual_plain_reduction_le_formal (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (P : ι → ℝ)
    (hP : ∀ i, 1 ≤ P i) :
    (∑ j, actualPlainReduction Z D a j) ≤ Real.logb Z (formalReductionFactor D a P) := by
  have h0 : (0:ℝ) < Ideal.absNorm (selectedPlain D a 0) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0)))
  have h1 : (0:ℝ) < Ideal.absNorm (selectedPlain D a 1) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
  have hprod : (1:ℝ) ≤ ∏ i∈frozenIndices D a, P i :=
    Finset.one_le_prod₀ (fun i _ => hP i)
  have hnorm := selectedNorm_pos D a
  have hle : selectedNorm D a ≤ formalReductionFactor D a P := by
    unfold formalReductionFactor
    nlinarith
  have hh := Real.logb_le_logb_of_le hZ hnorm hle
  rw [selectedNorm, Real.logb_mul h0.ne' h1.ne'] at hh
  simpa only [Fin.sum_univ_two, actualPlainReduction] using hh

theorem actual_clipped_reduction_nonneg (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (P : ι → ℝ)
    (hP : ∀ i, 1 ≤ P i) (x : Fin 2 → ℝ) :
    0 ≤ clippedReduction (Real.logb Z (formalReductionFactor D a P)) x
      (actualPlainReduction Z D a) :=
  clippedReduction_nonneg _ x _ (actual_plain_reduction_nonneg Z hZ D a)
    (actual_plain_reduction_le_formal Z hZ D a P hP)

/-- Both extraction scalars pay the residual projector's divisor dyad. No
divisibility of that projector into the reconstructed row is required. -/
theorem residual_projector_payment (t theta r₁ r₂ e₁ e₂ omega₁ omega₂ : ℝ)
    (x₁ a₁ x₂ a₂ : Fin 2 → ℝ)
    (hentrance₁ : t ≤ r₁+omega₁) (hentrance₂ : t ≤ r₂+omega₂)
    (herror₁ : |e₁+omega₁| ≤ theta) (herror₂ : |e₂+omega₂| ≤ theta)
    (hclip₁ : negativeTotal (fun i => x₁ i-a₁ i) ≤ theta)
    (hclip₂ : negativeTotal (fun i => x₂ i-a₂ i) ≤ theta) :
    t-(clippedReduction r₁ x₁ a₁+clippedReduction r₂ x₂ a₂)/2+
      (e₁+negativeTotal x₁+e₂+negativeTotal x₂)/2 ≤ 2*theta := by
  have he₁ := (abs_le.mp herror₁).2
  have he₂ := (abs_le.mp herror₂).2
  unfold clippedReduction
  linarith

theorem residual_high_saving (delta r₁ r₂ : ℝ) (hd : 0 ≤ delta)
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) : -delta*(r₁+r₂)/2 ≤ 0 := by
  nlinarith [mul_nonneg hd (add_nonneg h₁ h₂)]

theorem signed_rectangle_energy (a b : ℂ) :
    ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have hn := norm_sub_le a b
  have hs := pow_le_pow_left₀ (norm_nonneg (a-b)) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- Split both signed rectangles before attaching any clipped reduction to a
positive term. This is the four-pair Cauchy boundary used by the ledger. -/
theorem signed_rectangle_four_pairs (left right : Fin 2 → ℂ) :
    ‖(left 0-left 1)*star (right 0-right 1)‖^2 ≤
      4*∑ i, ∑ j, ‖left i‖^2*‖right j‖^2 := by
  have hl := signed_rectangle_energy (left 0) (left 1)
  have hr := signed_rectangle_energy (right 0) (right 1)
  have hh := mul_le_mul hl hr (sq_nonneg ‖right 0-right 1‖)
    (show 0 ≤ 2*(‖left 0‖^2+‖left 1‖^2) by positivity)
  rw [norm_mul, norm_star, mul_pow]
  simp only [Fin.sum_univ_two]
  nlinarith [hh]

/-- A finite row energy retains each of the four positive pairs. -/
theorem finite_signed_rectangle_four_pairs {α : Type*} (rows : Finset α)
    (weight : α → ℝ) (hw : ∀ u∈rows, 0 ≤ weight u)
    (left right : α → Fin 2 → ℂ) :
    (∑ u∈rows, weight u*‖(left u 0-left u 1)*star (right u 0-right u 1)‖^2) ≤
      4*∑ i, ∑ j, ∑ u∈rows, weight u*‖left u i‖^2*‖right u j‖^2 := by
  calc
    _ ≤ ∑ u∈rows, weight u*(4*∑ i, ∑ j, ‖left u i‖^2*‖right u j‖^2) :=
      Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left
        (signed_rectangle_four_pairs (left u) (right u)) (hw u hu))
    _ = _ := by
      simp only [Fin.sum_univ_two]
      simp_rw [← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

end
end Cycle63.Physical

#print axioms Cycle63.Physical.actual_clipped_reduction_nonneg
#print axioms Cycle63.Physical.extraction_scalar_rpow
#print axioms Cycle63.Physical.residual_projector_payment
#print axioms Cycle63.Physical.finite_signed_rectangle_four_pairs
