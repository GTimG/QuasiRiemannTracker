/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.LamSum

/-!
# Inverse.Poisson.InBallTotal — all in-ball labels (the main term of the Poisson step)

`∑_l w_l ‖inner_l‖ ≤ Γ₀ · ∫ M(t) (1+|t|)^(2d) dt`, where `M` dominates every kernel coefficient
`b_l` pointwise and `Γ₀` is the constant of `lam_sum_le`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap ENNReal
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

theorem sum_lintegral_le {L : Type*} (S : Finset L) (f : L → ℝ → ℝ≥0∞) :
    ∑ l ∈ S, ∫⁻ t, f l t ≤ ∫⁻ t, ∑ l ∈ S, f l t := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    calc (∫⁻ t, f a t) + ∑ l ∈ S, ∫⁻ t, f l t ≤ (∫⁻ t, f a t) + ∫⁻ t, ∑ l ∈ S, f l t := by gcongr
      _ ≤ ∫⁻ t, (f a t + ∑ l ∈ S, f l t) := le_lintegral_add _ _
      _ = ∫⁻ t, ∑ l ∈ insert a S, f l t := by
          congr 1; funext t; rw [Finset.sum_insert ha]

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem labelLam_nonneg (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι) (X : ℝ)
    (i : ℕ) (s₀ : ℝ) (y : O) (t : ℝ) :
    0 ≤ labelLam p hg pool Ψ m slots lists a Φ b' g X i s₀ y t := by
  unfold labelLam
  refine Finset.sum_nonneg fun χ _ => Finset.sum_nonneg fun η _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun t' _ => mul_nonneg (by norm_num) (add_nonneg ?_ ?_))
  · exact mul_nonneg (cellSW_nonneg p slots lists a g t' b') (cellSq_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _)
  · exact mul_nonneg (cellSW_nonneg p slots lists a g t' b') (cellSq_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- The in-ball total, given the per-label bound and the pointwise label-sum bound. -/
theorem inball_total {L : Type*} (S : Finset L) (w : L → ℝ) (hw0 : ∀ l ∈ S, 0 ≤ w l)
    (inn : L → ℂ) (Q : L → ℂ) (hQ : ∀ l ∈ S, ‖Q l‖ ≤ 1) (bof : L → ℝ → ℂ) (Λ : L → ℝ → ℝ)
    (hΛ : ∀ l t, 0 ≤ Λ l t) (M : ℝ → ℝ) (hbM : ∀ l ∈ S, ∀ t, ‖bof l t‖ ≤ M t)
    (hlabel : ∀ l ∈ S, ENNReal.ofReal ‖inn l‖ ≤
      ENNReal.ofReal ‖Q l‖ * ∫⁻ t, ENNReal.ofReal (‖bof l t‖ * Λ l t))
    (Γ : ℝ → ℝ) (hsum : ∀ t, ∑ l ∈ S, w l * Λ l t ≤ Γ t)
    (hint : Integrable (fun t => M t * Γ t)) (hM0 : ∀ t, 0 ≤ M t) :
    ∑ l ∈ S, w l * ‖inn l‖ ≤ ∫ t, M t * Γ t := by
  have hR : 0 ≤ ∫ t, M t * Γ t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (hM0 t) ((Finset.sum_nonneg fun l hl => mul_nonneg (hw0 l hl) (hΛ l t)).trans
      (hsum t))
  rw [← ENNReal.ofReal_le_ofReal_iff hR, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun t => mul_nonneg (hM0 t) ((Finset.sum_nonneg fun l hl =>
      mul_nonneg (hw0 l hl) (hΛ l t)).trans (hsum t)))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun l hl => mul_nonneg (hw0 l hl) (norm_nonneg _))]
  calc ∑ l ∈ S, ENNReal.ofReal (w l * ‖inn l‖)
      ≤ ∑ l ∈ S, ∫⁻ t, ENNReal.ofReal (w l * (M t * Λ l t)) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [ENNReal.ofReal_mul (hw0 l hl)]
        calc ENNReal.ofReal (w l) * ENNReal.ofReal ‖inn l‖
            ≤ ENNReal.ofReal (w l) *
              (ENNReal.ofReal ‖Q l‖ * ∫⁻ t, ENNReal.ofReal (‖bof l t‖ * Λ l t)) := by
              gcongr; exact hlabel l hl
          _ ≤ ENNReal.ofReal (w l) * (1 * ∫⁻ t, ENNReal.ofReal (M t * Λ l t)) := by
              have hQ1 : ENNReal.ofReal ‖Q l‖ ≤ 1 := by
                rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hQ l hl)
              have hI : ∫⁻ t, ENNReal.ofReal (‖bof l t‖ * Λ l t) ≤
                  ∫⁻ t, ENNReal.ofReal (M t * Λ l t) :=
                lintegral_mono fun t => ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right (hbM l hl t) (hΛ l t))
              exact mul_le_mul' le_rfl (mul_le_mul' hQ1 hI)
          _ = ∫⁻ t, ENNReal.ofReal (w l * (M t * Λ l t)) := by
              rw [one_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1; funext t
              rw [← ENNReal.ofReal_mul (hw0 l hl)]
    _ ≤ ∫⁻ t, ∑ l ∈ S, ENNReal.ofReal (w l * (M t * Λ l t)) := sum_lintegral_le S _
    _ ≤ ∫⁻ t, ENNReal.ofReal (M t * Γ t) := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [← ENNReal.ofReal_sum_of_nonneg (fun l hl => mul_nonneg (hw0 l hl)
          (mul_nonneg (hM0 t) (hΛ l t)))]
        apply ENNReal.ofReal_le_ofReal
        calc ∑ l ∈ S, w l * (M t * Λ l t) = M t * ∑ l ∈ S, w l * Λ l t := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
          _ ≤ M t * Γ t := mul_le_mul_of_nonneg_left (hsum t) (hM0 t)

end
end Qrh.MarkedAnchor.Inverse.Poisson
