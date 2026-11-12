/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.ChildRow

/-!
# Inverse.Poisson.RowSep — the profile separation inside a residual row

`mobiusRowF (· ↦ W(N g · N t · n/X) e(h, log(N g N t n/X))) z
   = ∫ b'(τ) e(τ+h, log r) · mobiusChildRowInj … (childLogTest Φ (τ+h)) Xc true z dτ`,
`N g N t / X = r / Xc`, `r ∈ [1, 2]`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

theorem logPhase_continuous_add (c x : ℝ) : Continuous (fun τ : ℝ => logPhase (τ + c) x) :=
  logPhase_continuous_freq c x

/-- Integrability of a Schwartz coefficient against a unimodular log-phase times a constant. -/
theorem integrable_schwartz_phase (b : 𝓢(ℝ, ℂ)) (c x : ℝ) (K : ℂ) :
    Integrable (fun τ : ℝ => b τ * (logPhase (τ + c) x * K)) := by
  refine (b.integrable).mul_bdd (c := ‖K‖) ?_ (ae_of_all _ ?_)
  · exact ((logPhase_continuous_add c x).mul continuous_const).aestronglyMeasurable
  · intro τ; rw [norm_mul, logPhase_norm, one_mul]

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem rowF_profile_sep (W Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Gn Tn X Xc r h : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hXc : 0 < Xc)
    (hrel : Gn * Tn / X = r / Xc) (z : O) :
    mobiusRowF p hg pool ψ m slots lists a
      (fun n => W (Gn * (Tn * n) / X) * logPhase h (Real.log (Gn * (Tn * n) / X))) z =
      ∫ τ : ℝ, b' τ * (logPhase (τ + h) (Real.log r) *
        mobiusChildRowInj p hg pool ψ m slots lists a (childLogTest Φ (τ + h)) Xc true z) := by
  unfold mobiusRowF mobiusChildRowInj
  simp only [if_true, Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro A _
    have hN := FirstPassCubeLabels.primeProductNorm_pos p hp A
    have hx : 0 < primeProductNorm p A / Xc := div_pos hN hXc
    have harg : Gn * (Tn * primeProductNorm p A) / X = r * (primeProductNorm p A / Xc) := by
      calc Gn * (Tn * primeProductNorm p A) / X = (Gn * Tn / X) * primeProductNorm p A := by ring
        _ = r / Xc * primeProductNorm p A := by rw [hrel]
        _ = r * (primeProductNorm p A / Xc) := by ring
    rw [harg, hb' r _ h hr1 hr2 hx]
    set K : ℂ := supportMobius (fun i => Ideal.span {p i}) A * ψ (∏ i ∈ A, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) A m *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z) * primeMarkInj slots lists a A
    set S : ℂ := (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)
    calc K * (∫ t : ℝ, logPhase (t + h) (Real.log r) *
          childLogTest Φ (t + h) (primeProductNorm p A / Xc) * b' t) * S
        = ∫ t : ℝ, K * (logPhase (t + h) (Real.log r) *
          childLogTest Φ (t + h) (primeProductNorm p A / Xc) * b' t) * S := by
          rw [← integral_const_mul, ← integral_mul_const]
      _ = _ := by
          apply integral_congr_ae
          filter_upwards with τ
          ring
  · intro A _
    have hint := integrable_schwartz_phase b' h (Real.log r)
      (supportMobius (fun i => Ideal.span {p i}) A * ψ (∏ i ∈ A, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) A m *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z) * primeMarkInj slots lists a A *
        Φ (primeProductNorm p A / Xc) * (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ))
    refine (hint.mul_bdd (g := fun τ : ℝ => logPhase (τ + h) (Real.log (primeProductNorm p A / Xc)))
      (c := 1) ?_ (ae_of_all _ ?_)).congr (ae_of_all _ ?_)
    · exact (logPhase_continuous_add h _).aestronglyMeasurable
    · intro τ; rw [logPhase_norm]
    · intro τ
      simp only [childLogTest]
      ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
