/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.SideBound

/-!
# Inverse.Poisson.SepBilBound — the separated bilinear form bounded by child squares

* `sideA_eq`, `sideB_eq`: the two projector sides are `sideSum`s with the twists
  `conjugateRayMonoid χ * Ψ` at the row `-y` and `rayMonoid η * Ψ` at `y`.
* `sepBil_norm_le`: `‖sepBil t‖ ≤ ∑_{χ,η} |crossCoeff| ∑_t' ‖side_A‖ ‖side_B‖`.
* `weighted_cauchy`: `(∑ w ∫|b'| f)² ≤ (∑ w ∫|b'|)(∑ w ∫|b'| f²)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open MixedCrossSeparation (columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

/-- Weighted Cauchy–Schwarz for finitely many weighted integrals against `|b'|`. -/
theorem weighted_cauchy {κ : Type*} (cells : Finset κ) (w : κ → ℝ) (hw : ∀ c, 0 ≤ w c)
    (b' : 𝓢(ℝ, ℂ)) (f : κ → ℝ → ℝ) (hf0 : ∀ c τ, 0 ≤ f c τ) (hfc : ∀ c, Continuous (f c))
    (B : κ → ℝ) (hfb : ∀ c τ, f c τ ≤ B c) :
    (∑ c ∈ cells, w c * ∫ τ : ℝ, ‖b' τ‖ * f c τ) ^ 2 ≤
      (∑ c ∈ cells, w c * ∫ τ : ℝ, ‖b' τ‖) *
        (∑ c ∈ cells, w c * ∫ τ : ℝ, ‖b' τ‖ * f c τ ^ 2) := by
  have hb : Integrable (fun τ : ℝ => ‖b' τ‖) := (b'.integrable (μ := volume)).norm
  have hbd : ∀ c, Integrable (fun τ => ‖b' τ‖ * f c τ) := fun c =>
    hb.mul_bdd (c := B c) (hfc c).aestronglyMeasurable (ae_of_all _ fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 c τ)]; exact hfb c τ)
  have hbd2 : ∀ c, Integrable (fun τ => ‖b' τ‖ * f c τ ^ 2) := fun c =>
    hb.mul_bdd (c := B c ^ 2) ((hfc c).pow 2).aestronglyMeasurable (ae_of_all _ fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf0 c τ) 2)]
      exact pow_le_pow_left₀ (hf0 c τ) (hfb c τ) 2)
  have h := QRH.SilDensitySplit.CommonProfile.cauchy_cells volume cells
    (fun c τ => w c * ‖b' τ‖) f (fun c τ => mul_nonneg (hw c) (norm_nonneg _)) hf0
    (fun c _ => hb.const_mul (w c))
    (fun c _ => ((hbd c).const_mul (w c)).congr (ae_of_all _ fun τ => by ring))
    (fun c _ => ((hbd2 c).const_mul (w c)).congr (ae_of_all _ fun τ => by ring))
  have e1 : ∀ c, ∫ τ : ℝ, w c * ‖b' τ‖ * f c τ = w c * ∫ τ : ℝ, ‖b' τ‖ * f c τ := by
    intro c; rw [← integral_const_mul]; congr 1; funext τ; ring
  have e2 : ∀ c, ∫ τ : ℝ, w c * ‖b' τ‖ = w c * ∫ τ : ℝ, ‖b' τ‖ := fun c => integral_const_mul _ _
  have e3 : ∀ c, ∫ τ : ℝ, w c * ‖b' τ‖ * f c τ ^ 2 = w c * ∫ τ : ℝ, ‖b' τ‖ * f c τ ^ 2 := by
    intro c; rw [← integral_const_mul]; congr 1; funext τ; ring
  simp only [e1, e2, e3] at h
  exact h

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem row_neg (S : Finset ι) (y : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-y)) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S y) := by
  rw [show -y = -1 * y by ring, finiteSquarefreeRow_mul, star_mul, star_row_neg_one, mul_comm]

theorem sideA_eq (pool g t : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X h : ℝ) (y : O) (χ : RayCharacter) :
    ∑ a' ∈ ((pool \ g) \ t).powerset,
      star (rayCharacter χ (∏ i ∈ t ∪ a', p i)) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (t ∪ a') (-1) *
        sepCol p hp hcop hg Ψ m slots lists a W g X y h (t ∪ a') =
      sideSum p hp hcop hg pool g t (conjugateRayMonoid χ * Ψ) m slots lists a
        (sideF W (primeProductNorm p g) X h) (-y) := by
  unfold sideSum
  apply Finset.sum_congr rfl
  intro a' _
  rw [row_neg p hg]
  simp only [sepCol, colCore, sideF, colX, MonoidHom.mul_apply,
    SecondPassArithmetic.conjugateRayMonoid_apply]
  ring

theorem sideB_eq (pool g t : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X h : ℝ) (y : O) (η : RayCharacter) :
    ∑ b' ∈ ((pool \ g) \ t).powerset,
      rayCharacter η (∏ i ∈ t ∪ b', p i) *
        sepCol p hp hcop hg Ψ m slots lists a W g X y h (t ∪ b') =
      sideSum p hp hcop hg pool g t (rayMonoid η * Ψ) m slots lists a
        (sideF W (primeProductNorm p g) X h) y := by
  unfold sideSum
  apply Finset.sum_congr rfl
  intro b' _
  simp only [sepCol, colCore, sideF, colX, MonoidHom.mul_apply,
    SecondPassArithmetic.rayMonoid_apply]
  ring

include hp hcop in
theorem sepBil_norm_le (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (g : Finset ι) (X s₀ : ℝ) (y : O) (t : ℝ) :
    ‖sepBil p hp hcop hg pool Ψ m slots lists a W g X s₀ y t‖ ≤
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖ *
        ∑ t' ∈ (pool \ g).powerset,
          ‖sideSum p hp hcop hg pool g t' (conjugateRayMonoid χ * Ψ) m slots lists a
              (sideF W (primeProductNorm p g) X (s₀ + t)) (-y)‖ *
          ‖sideSum p hp hcop hg pool g t' (rayMonoid η * Ψ) m slots lists a
              (sideF W (primeProductNorm p g) X (s₀ - t)) y‖ := by
  unfold sepBil
  rw [pair_bilinear_expand p hp hcop hg hc (pool \ g)
    (sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ + t))
    (sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ - t))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η _ => ?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t' _ => ?_)
  rw [sideA_eq p hp hcop hg pool g t' Ψ m slots lists a W X (s₀ + t) y χ,
    sideB_eq p hp hcop hg pool g t' Ψ m slots lists a W X (s₀ - t) y η]
  rw [norm_mul, norm_mul, norm_star, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end
end Qrh.MarkedAnchor.Inverse.Poisson
