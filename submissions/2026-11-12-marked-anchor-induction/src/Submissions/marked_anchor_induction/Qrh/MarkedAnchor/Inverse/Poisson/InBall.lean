/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.SepBilBound

/-!
# Inverse.Poisson.InBall — one label bounded by child squares

For one label `(f, g, E, k)` (dyadic block `2^i ≤ N g ≤ 2^(i+1)`):

`‖sepBil t‖ ≤ ∑_{χ,η} |cc| ∑_{t'} ½ (SW_A ∑_{θ,J} w ∫|b'| ‖chA‖² + SW_B ∑_{θ,J} w ∫|b'| ‖chB‖²)`

with `w = |gCoeff θ| |mark_J(g∪t')| /√N t'`, `SW = ∑_{θ,J} w ∫|b'|`, and the child rows
`chA = mobiusChildRowInj (pool\t') (rayMonoid θ * (conjugateRayMonoid χ * Ψ)) … (childLogTest Φ (τ+s₀+t)) Xc true (-y)`,
`chB = mobiusChildRowInj (pool\t') (rayMonoid θ * (rayMonoid η * Ψ)) … (childLogTest Φ (τ+s₀-t)) Xc true y`,
`Xc = X/(2^i N t')`.
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

theorem twist_norm_le (θ χ : RayCharacter) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (conj : Bool) :
    ∀ u, ‖(rayMonoid θ * ((if conj then conjugateRayMonoid χ else rayMonoid χ) * Ψ)) u‖ ≤ 1 := by
  intro u
  simp only [MonoidHom.mul_apply, norm_mul]
  have h1 : ‖rayMonoid θ u‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one θ _
  have h2 : ‖(if conj then conjugateRayMonoid χ else rayMonoid χ) u‖ ≤ 1 := by
    split_ifs
    · rw [SecondPassArithmetic.conjugateRayMonoid_apply, norm_star]
      exact FiniteRayExpansion.norm_char_le_one χ _
    · exact FiniteRayExpansion.norm_char_le_one χ _
  calc ‖rayMonoid θ u‖ * (‖(if conj then conjugateRayMonoid χ else rayMonoid χ) u‖ * ‖Ψ u‖)
      ≤ 1 * (1 * 1) := by gcongr; exact hΨ u
    _ = 1 := by ring

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The weight of a (θ, J) cell. -/
def cellW (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (g t : Finset ι)
    (c : RayCharacter × Finset σ) : ℝ :=
  ‖gCoeff c.1‖ * ‖primeMarkInj c.2 lists a (g ∪ t)‖ * (Real.sqrt (primeProductNorm p t))⁻¹

/-- The child row of a cell at height `h`, twist `ψ₀`, row `z`. -/
def cellChild (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc h : ℝ) (z : O) (c : RayCharacter × Finset σ) (τ : ℝ) : ℝ :=
  ‖mobiusChildRowInj p hg (pool \ t) (rayMonoid c.1 * ψ₀) m (slots \ c.2) lists a
    (childLogTest Φ (τ + h)) Xc true z‖

theorem side_sq_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (W Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (pool g t : Finset ι) (ht : t ⊆ pool \ g) (ψ₀ : O →* ℂ)
    (hψ₀ : ∀ θ : RayCharacter, ∀ u, ‖(rayMonoid θ * ψ₀) u‖ ≤ 1) (hψ₀' : ∀ u, ‖ψ₀ u‖ ≤ 1)
    (m : O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (X r Xc h : ℝ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hXc : 0 < Xc)
    (hrel : primeProductNorm p g * primeProductNorm p t / X = r / Xc) (z : O)
    (hz : ∀ i ∈ g, z ∈ Ideal.span {p i}) :
    ‖sideSum p hp hcop hg pool g t ψ₀ m slots lists a (sideF W (primeProductNorm p g) X h) z‖ ^ 2 ≤
      (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        cellW p slots lists a g t c * ∫ τ : ℝ, ‖b' τ‖) *
      (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        cellW p slots lists a g t c *
          ∫ τ : ℝ, ‖b' τ‖ * cellChild p hg pool t ψ₀ m slots lists a Φ Xc h z c τ ^ 2) := by
  have hb := side_bound p hp hcop hg hinj hc hpr W Φ b' hb' pool g t ht ψ₀ hψ₀' m slots lists a
    X r Xc h hr1 hr2 hXc hrel z hz
  rw [← Finset.sum_product'] at hb
  have hcs := weighted_cauchy ((Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (cellW p slots lists a g t) (fun c => by unfold cellW; positivity) b'
    (cellChild p hg pool t ψ₀ m slots lists a Φ Xc h z) (fun c τ => norm_nonneg _)
    (fun c => (childRow_continuous p hg _ _ m _ lists a Φ h Xc true z).norm)
    (fun c => childTriv p (pool \ t) (slots \ c.2) lists a Φ Xc)
    (fun c τ => childRow_norm_le p hg hinj _ _ (hψ₀ c.1) m _ lists a Φ _ Xc true z)
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (hb.trans (le_of_eq ?_)) 2) hcs
  apply Finset.sum_congr rfl
  intro c _
  rfl

end
end Qrh.MarkedAnchor.Inverse.Poisson
