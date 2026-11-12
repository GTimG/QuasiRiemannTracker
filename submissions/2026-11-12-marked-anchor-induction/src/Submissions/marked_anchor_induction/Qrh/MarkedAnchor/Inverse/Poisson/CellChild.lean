/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.LamLabel

/-!
# Inverse.Poisson.CellChild — one cell paid by the child hypothesis

`∑_{y ∈ ball} cellF(c, i, y) ≤ B (1+|h|)^(2d) ∫ |b'(τ)| (1+|τ|)^(2d)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)

local notation "O" => ActualEisensteinCubic.O

theorem one_add_abs_add_le (x y : ℝ) : 1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have := norm_add_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem one_add_pow_add_le (x y : ℝ) (n : ℕ) :
    (1 + ‖x + y‖) ^ n ≤ (1 + ‖x‖) ^ n * (1 + ‖y‖) ^ n := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_abs_add_le x y) n

theorem schwartz_weight_integrable (b : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun τ : ℝ => ‖b τ‖ * (1 + ‖τ‖) ^ n) := by
  have h0 : Integrable (fun τ : ℝ => ‖b τ‖) := (b.integrable (μ := volume)).norm
  have hn : Integrable (fun τ : ℝ => ‖τ‖ ^ n * ‖b τ‖) := b.integrable_pow_mul volume n
  refine Integrable.mono' ((h0.add hn).const_mul (2 ^ n)) ?_ (ae_of_all _ ?_)
  · exact ((b.continuous.norm).mul ((continuous_const.add continuous_norm).pow n)).aestronglyMeasurable
  · intro τ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := one_add_pow_le_two_pow ‖τ‖ (norm_nonneg τ) n
    have hb := norm_nonneg (b τ)
    calc ‖b τ‖ * (1 + ‖τ‖) ^ n ≤ ‖b τ‖ * (2 ^ n * (1 + ‖τ‖ ^ n)) :=
          mul_le_mul_of_nonneg_left this hb
      _ = 2 ^ n * (‖b τ‖ + ‖τ‖ ^ n * ‖b τ‖) := by ring

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem cell_child_sum_le (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (d : ℕ) (Z X bo Hc B : ℝ)
    (hX : 0 < X) (hB : 0 ≤ B) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (t : Finset ι) (ht : t ∈ pool.powerset) (ψ₀ : O →* ℂ) (c : RayCharacter × Finset σ)
    (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (hψ : IsChildRay Ψ (rayMonoid c.1 * ψ₀)) (i : ℕ) (hok : cellOK p lists X i t c.2) (h τ : ℝ) :
    ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      cellChild p hg pool t ψ₀ m slots lists a Φ (X / (2 ^ i * primeProductNorm p t)) h y c τ ^ 2
      ≤ B * (1 + ‖τ + h‖) ^ (2 * d) := by
  by_cases hN : primeProductNorm p t ≤ 2 * bo * X
  · have hNt := FirstPassCubeLabels.primeProductNorm_pos p hp t
    have hXc : 0 < X / (2 ^ i * primeProductNorm p t) := by positivity
    have hXle : X / (2 ^ i * primeProductNorm p t) ≤ X := by
      apply div_le_self hX.le
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
        (one_le_primeProductNorm p hp t)
    have h := hchild t ht hN c.2 (Finset.mem_product.mp hc).2 (rayMonoid c.1 * ψ₀) hψ 0
      (τ + h) _ hXc hXle hok true
    unfold mobiusChildSumInj at h
    simpa [cellChild] using h
  · have hgt : 2 * bo * X < primeProductNorm p t := lt_of_not_ge hN
    have hz : ∀ y, cellChild p hg pool t ψ₀ m slots lists a Φ
        (X / (2 ^ i * primeProductNorm p t)) h y c τ = 0 := by
      intro y
      unfold cellChild
      rw [childRow_zero_large p hp hg pool t _ m _ lists a Φ bo X i _ y hX hΦ hgt, norm_zero]
    simp only [hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

include hp in
theorem cellF_sum_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (d : ℕ) (Z X bo Hc B : ℝ)
    (hX : 0 < X) (hB : 0 ≤ B) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (t : Finset ι) (ht : t ∈ pool.powerset) (ψ₀ : O →* ℂ) (c : RayCharacter × Finset σ)
    (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (hψ : IsChildRay Ψ (rayMonoid c.1 * ψ₀)) (hψn : ∀ u, ‖(rayMonoid c.1 * ψ₀) u‖ ≤ 1)
    (i : ℕ) (hok : cellOK p lists X i t c.2) (h : ℝ) :
    ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      cellF p hg pool t ψ₀ m slots lists a Φ b' X h c i y ≤
        B * (1 + ‖h‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) := by
  unfold cellF
  set Xc := X / (2 ^ i * primeProductNorm p t)
  have hb0 : Integrable (fun τ : ℝ => ‖b' τ‖) := (b'.integrable (μ := volume)).norm
  have hint : ∀ y, Integrable (fun τ : ℝ => ‖b' τ‖ * cellChild p hg pool t ψ₀ m slots lists a Φ
      Xc h y c τ ^ 2) := by
    intro y
    refine hb0.mul_bdd (c := childTriv p (pool \ t) (slots \ c.2) lists a Φ Xc ^ 2) ?_
      (ae_of_all _ fun τ => ?_)
    · exact (((childRow_continuous p hg _ _ m _ lists a Φ h Xc true y).norm).pow 2).aestronglyMeasurable
    · unfold cellChild
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (childRow_norm_le p hg hinj _ _ hψn m _ lists a Φ _ Xc true y) 2
  rw [← integral_finset_sum _ (fun y _ => hint y), ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ fun τ => Finset.sum_nonneg fun y _ => by positivity
  · exact (schwartz_weight_integrable b' (2 * d)).const_mul _
  · refine ae_of_all _ fun τ => ?_
    have hcs := cell_child_sum_le p hp hg pool Ψ m slots lists a Φ d Z X bo Hc B hX hB hΦ hchild
      t ht ψ₀ c hc hψ i hok h τ
    have hpw := one_add_pow_add_le τ h (2 * d)
    have hbn := norm_nonneg (b' τ)
    calc ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
          ‖b' τ‖ * cellChild p hg pool t ψ₀ m slots lists a Φ Xc h y c τ ^ 2
        = ‖b' τ‖ * ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
          cellChild p hg pool t ψ₀ m slots lists a Φ Xc h y c τ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ‖b' τ‖ * (B * (1 + ‖τ + h‖) ^ (2 * d)) := mul_le_mul_of_nonneg_left hcs hbn
      _ ≤ ‖b' τ‖ * (B * ((1 + ‖τ‖) ^ (2 * d) * (1 + ‖h‖) ^ (2 * d))) := by gcongr
      _ = B * (1 + ‖h‖) ^ (2 * d) * (‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) := by ring

include hp in
/-- The gated cell: the child hypothesis is used only on admissible cells. -/
theorem cellG_sum_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (d : ℕ) (Z X bo Hc B : ℝ)
    (hX : 0 < X) (hB : 0 ≤ B) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (t : Finset ι) (ht : t ∈ pool.powerset) (ψ₀ : O →* ℂ) (c : RayCharacter × Finset σ)
    (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (hψ : IsChildRay Ψ (rayMonoid c.1 * ψ₀)) (hψn : ∀ u, ‖(rayMonoid c.1 * ψ₀) u‖ ≤ 1)
    (i : ℕ) (h : ℝ) :
    ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i y ≤
        B * (1 + ‖h‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) := by
  unfold cellG
  by_cases hok : cellOK p lists X i t c.2
  · simp only [if_pos hok]
    exact cellF_sum_le p hp hg hinj pool Ψ m slots lists a Φ b' d Z X bo Hc B hX hB hΦ hchild
      t ht ψ₀ c hc hψ hψn i hok h
  · simp only [if_neg hok, Finset.sum_const_zero]
    have : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) := integral_nonneg fun τ => by positivity
    positivity

end
end Qrh.MarkedAnchor.Inverse.Poisson
