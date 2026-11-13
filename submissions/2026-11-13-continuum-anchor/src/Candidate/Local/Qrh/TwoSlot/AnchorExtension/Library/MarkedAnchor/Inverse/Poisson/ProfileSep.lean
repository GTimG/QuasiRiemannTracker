/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Separation
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Statement

/-!
# Inverse.Poisson.ProfileSep — the dyadic profile separation

For the canonical profile `W` (support `[ao, bo]`) and a dyadic ratio `r ∈ [1, 2]`
(`N g = 2^i r`):

`W(r x) · logPhase h (log (r x)) = ∫ logPhase (t+h) (log r) · childLogTest Φ (t+h) x · b(t) dt`

with ONE fixed Schwartz coefficient `b` and the fixed bump `Φ = 1` on `[ao/2, bo]`. So the child
profile is the fixed `Φ`, at the label-independent scale `Xc = X/(2^i N t)`, at height `t+h`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open MeasureTheory OAI OAI.SevenEighths.InverseMoment
open scoped FourierTransform SchwartzMap ContDiff

theorem logPhase_add_freq (t s x : ℝ) :
    FourierBridge.logPhase (t + s) x = FourierBridge.logPhase t x * FourierBridge.logPhase s x := by
  unfold FourierBridge.logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem profile_separation (W : ℝ → ℂ) (hWs : ContDiff ℝ ∞ W) (ao bo : ℝ) (hao : 0 < ao)
    (hsupp : Function.support W ⊆ Set.Icc ao bo) (Φ : ℝ → ℂ)
    (hΦ1 : ∀ x ∈ Set.Icc (ao / 2) bo, Φ x = 1)
    (hΦsupp : Function.support Φ ⊆ Set.Icc (ao / 4) (2 * bo)) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t := by
  let M : Fin 2 → ℝ := ![Real.log 2, max |Real.log (ao / 4)| |Real.log (2 * bo)|]
  let a : Fin 2 → ℝ := fun _ => 1
  let T : ℝ := ∑ j : Fin 2, |a j| * M j
  have hM : ∀ j, 0 ≤ M j := by
    intro j; fin_cases j
    · simp [M]; exact Real.log_nonneg (by norm_num)
    · simp [M]
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hM j)
  obtain ⟨V, hVc, hVs, hVone, _, _⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let win : Fin 2 → ℝ → ℂ :=
    ![fun z => if 0 ≤ z ∧ z ≤ Real.log 2 then 1 else 0, fun z => Φ (Real.exp z)]
  have hwin : ∀ j z, win j z ≠ 0 → |z| ≤ M j := by
    intro j z hz
    match j with
    | 0 =>
      simp only [win, Matrix.cons_val_zero, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        not_not] at hz
      simp only [M, Matrix.cons_val_zero]
      rw [abs_of_nonneg hz.1]; exact hz.2
    | 1 =>
      simp only [win, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at hz
      have hmem := hΦsupp hz
      simp only [M, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      have h1 : Real.log (ao / 4) ≤ z := by
        rw [← Real.log_exp z]; exact Real.log_le_log (by positivity) hmem.1
      have h2 : z ≤ Real.log (2 * bo) := by
        rw [← Real.log_exp z]; exact Real.log_le_log (Real.exp_pos z) hmem.2
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log (ao / 4))
        have := le_max_left |Real.log (ao / 4)| |Real.log (2 * bo)|
        linarith
      · have := le_abs_self (Real.log (2 * bo))
        have := le_max_right |Real.log (ao / 4)| |Real.log (2 * bo)|
        linarith
  refine ⟨𝓕 (FourierBridge.logProfile V W 1 1 hVc hVs hWs), ?_⟩
  intro r x h hr1 hr2 hx
  have hr0 : 0 < r := by linarith
  let y : Fin 2 → ℝ := ![Real.log r, Real.log x]
  have hactive : (∏ j : Fin 2, win j (y j)) ≠ 0 → V (∑ j : Fin 2, a j * y j) = 1 :=
    FourierBridge.coupled_cutoff_active win V a y M hwin (by simpa [T] using hVone)
  have key := FourierBridge.coupled_log_separation win W V 1 a y hVc hVs hWs hactive
  have hw0 : win 0 (Real.log r) = 1 := by
    simp only [win, Matrix.cons_val_zero]
    rw [if_pos ⟨Real.log_nonneg hr1, Real.log_le_log hr0 hr2⟩]
  have hexp : Real.exp (∑ j : Fin 2, a j * y j) = r * x := by
    simp only [a, y, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_mul]
    rw [Real.exp_add, Real.exp_log hr0, Real.exp_log hx]
  have hΦW : Φ x * W (r * x) = W (r * x) := by
    by_cases hW : W (r * x) = 0
    · rw [hW, mul_zero]
    · have hmem := hsupp hW
      have hx1 : ao / 2 ≤ x := by
        have : ao ≤ r * x := hmem.1
        nlinarith
      have hx2 : x ≤ bo := by
        have : r * x ≤ bo := hmem.2
        nlinarith
      rw [hΦ1 x ⟨hx1, hx2⟩, one_mul]
  simp only [Fin.prod_univ_two, hexp, one_mul] at key
  simp only [y, win, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Real.exp_log hx, a, one_mul] at key
  rw [if_pos ⟨Real.log_nonneg hr1, Real.log_le_log hr0 hr2⟩, one_mul, hΦW] at key
  rw [key, Real.log_mul hr0.ne' hx.ne', FourierBridge.logPhase_add, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  simp only [childLogTest, logPhase_add_freq]
  ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
