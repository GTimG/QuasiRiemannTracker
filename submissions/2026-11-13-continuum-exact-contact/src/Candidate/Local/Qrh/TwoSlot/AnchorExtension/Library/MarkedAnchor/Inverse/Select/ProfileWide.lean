/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.ProfileSep

/-!
# Inverse.Select.ProfileWide — profile separation on a ratio window `[2^(-Kb), 1]`

Variant of `Poisson.ProfileSep.profile_separation` (same proof, wider window for `log r`): for the
canonical profile `W` (support `[ao, bo]`) and every ratio `r` with `1 ≤ 2^Kb r ≤ 2^Kb`,

`W(r x) · logPhase h (log (r x)) = ∫ logPhase (t+h) (log r) · childLogTest Φ (t+h) x · b(t) dt`

with ONE Schwartz `b` (depending on `Kb`) and a bump `Φ = 1` on `[ao, 2^Kb bo]`. In the selection
`r = N(img d)/∏_R H` (one marked prime per selected slot, `N(img d) ∈ [∏H/2^|R|, ∏H]`), so the
child column scale `X/∏_R H` is independent of the tuple `d` and a single inner row serves all `d`.

Also: weighted integrability of Schwartz functions.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open MeasureTheory OAI OAI.SevenEighths.InverseMoment
open scoped FourierTransform SchwartzMap ContDiff

theorem profile_separation_wide (W : ℝ → ℂ) (hWs : ContDiff ℝ ∞ W) (ao bo : ℝ) (hao : 0 < ao)
    (hsupp : Function.support W ⊆ Set.Icc ao bo) (Kb : ℕ) (Φ : ℝ → ℂ)
    (hΦ1 : ∀ x ∈ Set.Icc ao (2^Kb * bo), Φ x = 1)
    (hΦsupp : Function.support Φ ⊆ Set.Icc (ao / 2) (2 * (2^Kb * bo))) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ r x h : ℝ, 1 ≤ 2^Kb * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t := by
  let M : Fin 2 → ℝ := ![(Kb:ℝ) * Real.log 2, max |Real.log (ao / 2)| |Real.log (2 * (2^Kb * bo))|]
  let a : Fin 2 → ℝ := fun _ => 1
  let T : ℝ := ∑ j : Fin 2, |a j| * M j
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hM : ∀ j, 0 ≤ M j := by
    intro j; fin_cases j
    · simp only [M, Fin.zero_eta, Matrix.cons_val_zero]; positivity
    · simp [M]
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hM j)
  obtain ⟨V, hVc, hVs, hVone, _, _⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let win : Fin 2 → ℝ → ℂ :=
    ![fun z => if -((Kb:ℝ) * Real.log 2) ≤ z ∧ z ≤ 0 then 1 else 0, fun z => Φ (Real.exp z)]
  have hwin : ∀ j z, win j z ≠ 0 → |z| ≤ M j := by
    intro j z hz
    fin_cases j
    · simp only [win, Fin.zero_eta, Matrix.cons_val_zero, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, not_not] at hz
      simp only [M, Fin.zero_eta, Matrix.cons_val_zero]
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    · simp only [win, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hz
      have hmem := hΦsupp hz
      simp only [M, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h1 : Real.log (ao / 2) ≤ z := by
        rw [← Real.log_exp z]; exact Real.log_le_log (by positivity) hmem.1
      have h2 : z ≤ Real.log (2 * (2^Kb * bo)) := by
        rw [← Real.log_exp z]; exact Real.log_le_log (Real.exp_pos z) hmem.2
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log (ao / 2))
        have := le_max_left |Real.log (ao / 2)| |Real.log (2 * (2^Kb * bo))|
        linarith
      · have := le_abs_self (Real.log (2 * (2^Kb * bo)))
        have := le_max_right |Real.log (ao / 2)| |Real.log (2 * (2^Kb * bo))|
        linarith
  refine ⟨𝓕 (FourierBridge.logProfile V W 1 1 hVc hVs hWs), ?_⟩
  intro r x h hr1 hr2 hx
  have h2K : (0:ℝ) < 2^Kb := by positivity
  have hr0 : 0 < r := by
    by_contra hneg
    push_neg at hneg
    have : (2:ℝ)^Kb * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2K.le hneg
    linarith
  have hlogr : -((Kb:ℝ) * Real.log 2) ≤ Real.log r ∧ Real.log r ≤ 0 := by
    constructor
    · have h := Real.log_nonneg hr1
      rw [Real.log_mul h2K.ne' hr0.ne', Real.log_pow] at h
      linarith
    · exact Real.log_nonpos hr0.le hr2
  let y : Fin 2 → ℝ := ![Real.log r, Real.log x]
  have hactive : (∏ j : Fin 2, win j (y j)) ≠ 0 → V (∑ j : Fin 2, a j * y j) = 1 :=
    FourierBridge.coupled_cutoff_active win V a y M hwin (by simpa [T] using hVone)
  have key := FourierBridge.coupled_log_separation win W V 1 a y hVc hVs hWs hactive
  have hexp : Real.exp (∑ j : Fin 2, a j * y j) = r * x := by
    simp only [a, y, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul]
    rw [Real.exp_add, Real.exp_log hr0, Real.exp_log hx]
  have hΦW : Φ x * W (r * x) = W (r * x) := by
    by_cases hW : W (r * x) = 0
    · rw [hW, mul_zero]
    · have hmem := hsupp hW
      have hx1 : ao ≤ x := by
        have : ao ≤ r * x := hmem.1
        nlinarith
      have hx2 : x ≤ 2^Kb * bo := by
        have : r * x ≤ bo := hmem.2
        have : x ≤ (2^Kb * r) * x := le_mul_of_one_le_left hx.le hr1
        nlinarith
      rw [hΦ1 x ⟨hx1, hx2⟩, one_mul]
  simp only [Fin.prod_univ_two, hexp, one_mul] at key
  simp only [y, win, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.exp_log hx, a, one_mul] at key
  rw [if_pos hlogr, one_mul, hΦW] at key
  rw [key, Real.log_mul hr0.ne' hx.ne', FourierBridge.logPhase_add, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  simp only [childLogTest, Poisson.logPhase_add_freq]
  ring

/-- Weighted integrability of a Schwartz function. -/
theorem schwartz_weight_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => ‖b t‖ * (1 + ‖t‖) ^ J) volume := by
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume := b.integrable_pow_mul volume J
  have hR : Integrable (fun t : ℝ => (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  refine hR.mono' ?_ ?_
  · exact (b.continuous.norm.mul ((continuous_const.add continuous_norm).pow J)).aestronglyMeasurable
  · filter_upwards with t
    have hpow := Poisson.one_add_pow_le_two_pow ‖t‖ (norm_nonneg t) J
    have hb := norm_nonneg (b t)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖b t‖ * (1 + ‖t‖) ^ J ≤ ‖b t‖ * (2 ^ J * (1 + ‖t‖ ^ J)) := by gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by ring

/-- A Schwartz function times a bounded continuous function is integrable. -/
theorem schwartz_mul_bounded_integrable (b : 𝓢(ℝ, ℂ)) (g : ℝ → ℂ) (hg : Continuous g) (B : ℝ)
    (hB : ∀ t, ‖g t‖ ≤ B) : Integrable (fun t : ℝ => b t * g t) volume := by
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  refine (hI0.mul_const B).mono' ?_ ?_
  · exact (b.continuous.mul hg).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.profile_separation_wide
