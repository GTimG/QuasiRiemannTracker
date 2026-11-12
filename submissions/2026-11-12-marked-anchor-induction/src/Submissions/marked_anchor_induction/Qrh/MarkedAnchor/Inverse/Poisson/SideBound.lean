/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.InnerBound
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Bilinear
import Submissions.sil_density_split_20261026.Analysis.CommonProfile

/-!
# Inverse.Poisson.SideBound — one side of the projector bounded by child rows

`‖side‖ ≤ ∑_θ ∑_J |gCoeff θ| |mark_J(g∪t)| / √N t · ∫ |b'(τ)| ‖child_{θ,J}(τ+h)‖ dτ`, the child
being `mobiusChildRowInj p hg (pool \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a (childLogTest Φ (τ+h))
Xc true z` with the label-independent scale `Xc = X/(2^i N t)` and the ORIGINAL pool minus `t`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open MixedCrossSeparation (columnG)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- One side of the projector in the general twisted form. -/
def sideSum (pool g t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (F : ℝ → ℂ) (z : O) : ℂ :=
  ∑ a' ∈ ((pool \ g) \ t).powerset,
    supportMobius (fun i => Ideal.span {p i}) (t ∪ a') * columnG p hp hcop hg (t ∪ a') *
      ψ₀ (∏ i ∈ t ∪ a', p i) * rowCoprimeMask (fun i => Ideal.span {p i}) (t ∪ a') m *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (t ∪ a') z) *
      primeMarkInj slots lists a (g ∪ (t ∪ a')) * F (primeProductNorm p (t ∪ a')) *
      (((Real.sqrt (primeProductNorm p (t ∪ a')))⁻¹ : ℝ) : ℂ)

/-- The norm profile of a side at height `h`. -/
def sideF (W : ℝ → ℂ) (Gn X h : ℝ) (n : ℝ) : ℂ :=
  W (Gn * n / X) * logPhase h (Real.log (Gn * n / X))

theorem gCoeff_mul_norm_le (θ : RayCharacter) (K : ℂ) (hK : ‖K‖ ≤ 1) :
    ‖gCoeff θ * K‖ ≤ ‖gCoeff θ‖ := by
  rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hK

theorem side_bound (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (W Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (pool g t : Finset ι) (ht : t ⊆ pool \ g) (ψ₀ : O →* ℂ) (hψ₀ : ∀ u, ‖ψ₀ u‖ ≤ 1) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (X r Xc h : ℝ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hXc : 0 < Xc)
    (hrel : primeProductNorm p g * primeProductNorm p t / X = r / Xc) (z : O)
    (hz : ∀ i ∈ g, z ∈ Ideal.span {p i}) :
    ‖sideSum p hp hcop hg pool g t ψ₀ m slots lists a (sideF W (primeProductNorm p g) X h) z‖ ≤
      ∑ θ : RayCharacter, ∑ J ∈ slots.powerset,
        ‖gCoeff θ‖ * ‖primeMarkInj J lists a (g ∪ t)‖ * (Real.sqrt (primeProductNorm p t))⁻¹ *
        ∫ τ : ℝ, ‖b' τ‖ * ‖mobiusChildRowInj p hg (pool \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
          (childLogTest Φ (τ + h)) Xc true z‖ := by
  unfold sideSum
  rw [side_expand p hp hcop hg hinj hc hpr g t (pool \ g) ht Finset.disjoint_sdiff ψ₀ m z slots
    lists a (sideF W (primeProductNorm p g) X h)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun θ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
  have hrow : mobiusRowF p hg ((pool \ g) \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
      (fun n => sideF W (primeProductNorm p g) X h (primeProductNorm p t * n)) z =
      ∫ τ : ℝ, b' τ * (logPhase (τ + h) (Real.log r) *
        mobiusChildRowInj p hg ((pool \ g) \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
          (childLogTest Φ (τ + h)) Xc true z) := by
    unfold sideF
    exact rowF_profile_sep p hp hg W Φ b' hb' _ _ m _ lists a _ _ X Xc r h hr1 hr2 hXc hrel z
  have hext : ∀ τ : ℝ, mobiusChildRowInj p hg ((pool \ g) \ t) (rayMonoid θ * ψ₀) m (slots \ J)
      lists a (childLogTest Φ (τ + h)) Xc true z =
      mobiusChildRowInj p hg (pool \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
        (childLogTest Φ (τ + h)) Xc true z := by
    intro τ
    rw [sdiff_sdiff_comm]
    exact childRow_pool_extend p hg (pool \ t) g _ m _ lists a _ Xc true z hz
  rw [hrow, norm_mul]
  have hs : 0 ≤ (Real.sqrt (primeProductNorm p t))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hscal : ‖gCoeff θ * primeMarkInj J lists a (g ∪ t) *
      (supportMobius (fun i => Ideal.span {p i}) t * rayCharacter θ (∏ i ∈ t, p i) *
        ψ₀ (∏ i ∈ t, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) t m *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg t z) *
        (((Real.sqrt (primeProductNorm p t))⁻¹ : ℝ) : ℂ))‖ ≤
      ‖gCoeff θ‖ * ‖primeMarkInj J lists a (g ∪ t)‖ * (Real.sqrt (primeProductNorm p t))⁻¹ := by
    have hray : ‖rayCharacter θ (∏ i ∈ t, p i)‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one θ _
    have hμ := supportMobius_norm p hinj t
    have hψt := hψ₀ (∏ i ∈ t, p i)
    have hm := rowCoprimeMask_norm_le p t m
    have hχ : ‖star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg t z)‖ ≤ 1 := by
      rw [norm_star]; exact finiteSquarefreeRow_norm_le_one _ hg t z
    simp only [norm_mul, hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, one_mul]
    have h1 := norm_nonneg (gCoeff θ)
    have h2 := norm_nonneg (primeMarkInj J lists a (g ∪ t))
    calc ‖gCoeff θ‖ * ‖primeMarkInj J lists a (g ∪ t)‖ *
          (‖rayCharacter θ (∏ i ∈ t, p i)‖ * ‖ψ₀ (∏ i ∈ t, p i)‖ *
            ‖rowCoprimeMask (fun i => Ideal.span {p i}) t m‖ *
            ‖star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg t z)‖ *
            (Real.sqrt (primeProductNorm p t))⁻¹)
        ≤ ‖gCoeff θ‖ * ‖primeMarkInj J lists a (g ∪ t)‖ *
          (1 * 1 * 1 * 1 * (Real.sqrt (primeProductNorm p t))⁻¹) := by gcongr
      _ = _ := by ring
  have hint : ‖∫ τ : ℝ, b' τ * (logPhase (τ + h) (Real.log r) *
        mobiusChildRowInj p hg ((pool \ g) \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
          (childLogTest Φ (τ + h)) Xc true z)‖ ≤
      ∫ τ : ℝ, ‖b' τ‖ * ‖mobiusChildRowInj p hg (pool \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
          (childLogTest Φ (τ + h)) Xc true z‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with τ
    rw [norm_mul, norm_mul, logPhase_norm, one_mul, hext τ]
  exact mul_le_mul hscal hint (norm_nonneg _) (by positivity)

end
end Qrh.MarkedAnchor.Inverse.Poisson
