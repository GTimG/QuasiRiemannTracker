/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.InBall
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Fibre

/-!
# Inverse.Poisson.LabelInt — one label as a `t`-integral of child squares

`ofReal ‖inner g E k‖ ≤ ofReal ‖Q_g‖ · ∫⁻ ofReal (‖b t‖ · Λ(t))`, with
`Λ(t) = ∑_{χ,η} |cc| ∑_{t'} ½ (SW(t') CA(χ,t',t) + SW(t') CB(η,t',t))`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

theorem twist_conj_le (θ χ : RayCharacter) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (u : O) :
    ‖(rayMonoid θ * (conjugateRayMonoid χ * Ψ)) u‖ ≤ 1 := by
  simpa using twist_norm_le θ χ Ψ hΨ true u

theorem twist_plain_le (θ χ : RayCharacter) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (u : O) :
    ‖(rayMonoid θ * (rayMonoid χ * Ψ)) u‖ ≤ 1 := by
  simpa using twist_norm_le θ χ Ψ hΨ false u

theorem twist1_conj_le (χ : RayCharacter) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (u : O) :
    ‖(conjugateRayMonoid χ * Ψ) u‖ ≤ 1 := by
  simp only [MonoidHom.mul_apply, norm_mul, SecondPassArithmetic.conjugateRayMonoid_apply,
    norm_star]
  calc ‖rayCharacter χ u‖ * ‖Ψ u‖ ≤ 1 * 1 := by
        gcongr
        · exact FiniteRayExpansion.norm_char_le_one χ _
        · exact hΨ u
    _ = 1 := one_mul 1

theorem twist1_plain_le (χ : RayCharacter) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (u : O) :
    ‖(rayMonoid χ * Ψ) u‖ ≤ 1 := by
  simp only [MonoidHom.mul_apply, norm_mul]
  calc ‖rayMonoid χ u‖ * ‖Ψ u‖ ≤ 1 * 1 := by
        gcongr
        · exact FiniteRayExpansion.norm_char_le_one χ _
        · exact hΨ u
    _ = 1 := one_mul 1

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The sum of the cell weights against `|b'|`. -/
def cellSW (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (g t : Finset ι)
    (b' : 𝓢(ℝ, ℂ)) : ℝ :=
  ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
    cellW p slots lists a g t c * ∫ τ : ℝ, ‖b' τ‖

/-- The weighted child squares of one side. -/
def cellSq (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (Xc h : ℝ) (z : O) : ℝ :=
  ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
    cellW p slots lists a g t c *
      ∫ τ : ℝ, ‖b' τ‖ * cellChild p hg pool t ψ₀ m slots lists a Φ Xc h z c τ ^ 2

/-- The `t`-density of one label. -/
def labelLam (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι) (X : ℝ) (i : ℕ) (s₀ : ℝ)
    (y : O) (t : ℝ) : ℝ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖ *
    ∑ t' ∈ (pool \ g).powerset, (1 / 2 : ℝ) *
      (cellSW p slots lists a g t' b' *
          cellSq p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' g
            (X / (2 ^ i * primeProductNorm p t')) (s₀ + t) (-y) +
        cellSW p slots lists a g t' b' *
          cellSq p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' g
            (X / (2 ^ i * primeProductNorm p t')) (s₀ - t) y)

theorem sq_mul_le (x y : ℝ) : x * y ≤ (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

theorem label_inner_bound (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (Wk : 𝓢(ℝ, ℂ)) (Y X s₀ : ℝ) (hX : 0 < X) (f : O) (g E : Finset ι) (hE : E ⊆ g)
    (k : O) (i : ℕ) (hi1 : (2 : ℝ) ^ i ≤ primeProductNorm p g)
    (hi2 : primeProductNorm p g ≤ 2 * 2 ^ i)
    (b : ℝ → ℂ) (hbint : Integrable b) (hb : KernelSep Wk W (poissonR p Y X g E k) b) :
    ENNReal.ofReal ‖inner p hp hcop hg pool Ψ m f (entryH p slots lists a W s₀ X) Wk Y g E k‖ ≤
      ENNReal.ofReal ‖star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
          canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ *
        ∫⁻ t : ℝ, ENNReal.ofReal (‖b t‖ *
          labelLam p hg pool Ψ m slots lists a Φ b' g X i s₀ (physRow p f g E k) t) := by
  rw [inner_eq_integral p hp hcop hg pool Ψ m f slots lists a W Wk Y X s₀ hX g E k b hbint hb,
    norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  gcongr
  refine (ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)).trans
    (ENNReal.ofReal_toReal_le.trans ?_)
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (sepBil_norm_le p hp hcop hg hc pool Ψ m slots lists a W g X s₀ _ t).trans ?_
  unfold labelLam
  apply Finset.sum_le_sum; intro χ _
  apply Finset.sum_le_sum; intro η _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum; intro t' ht'
  have ht'g : t' ⊆ pool \ g := Finset.mem_powerset.mp ht'
  have hr1 : 1 ≤ primeProductNorm p g / 2 ^ i := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hr2 : primeProductNorm p g / 2 ^ i ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hNt := FirstPassCubeLabels.primeProductNorm_pos p hp t'
  have hXc : 0 < X / (2 ^ i * primeProductNorm p t') := by positivity
  have hrel : primeProductNorm p g * primeProductNorm p t' / X =
      (primeProductNorm p g / 2 ^ i) / (X / (2 ^ i * primeProductNorm p t')) := by
    field_simp
  have hzA : ∀ j ∈ g, -physRow p f g E k ∈ Ideal.span {p j} :=
    fun j hj => neg_physRow_mem_span p f g E hE k j hj
  have hzB : ∀ j ∈ g, physRow p f g E k ∈ Ideal.span {p j} :=
    fun j hj => physRow_mem_span p f g E hE k j hj
  have hA := side_sq_le p hp hcop hg hinj hc hpr W Φ b' hb' pool g t' ht'g
    (conjugateRayMonoid χ * Ψ) (fun θ u => twist_conj_le θ χ Ψ hΨ u)
    (twist1_conj_le χ Ψ hΨ) m slots lists a X _ _ (s₀ + t) hr1 hr2 hXc hrel _ hzA
  have hB := side_sq_le p hp hcop hg hinj hc hpr W Φ b' hb' pool g t' ht'g
    (rayMonoid η * Ψ) (fun θ u => twist_plain_le θ η Ψ hΨ u)
    (twist1_plain_le η Ψ hΨ) m slots lists a X _ _ (s₀ - t) hr1 hr2 hXc hrel _ hzB
  refine (sq_mul_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add hA hB

end
end Qrh.MarkedAnchor.Inverse.Poisson
