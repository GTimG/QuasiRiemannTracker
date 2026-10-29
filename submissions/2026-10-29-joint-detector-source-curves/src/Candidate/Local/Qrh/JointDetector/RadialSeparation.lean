/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients

/-! Actual radial-transform separation on fixed dyadic row/source windows.
The integration variable produces only unit phases in the three independent
norm variables. The L1 envelope is uniform in the physical scale R. -/

namespace Qrh.JointDetector
noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI EisensteinSchwartzPoisson

private def logWindow (y : ℝ) : ℂ :=
  if |y| ≤ Real.log 2 then 1 else 0

private def pairSigns : Fin 3 → ℝ := ![-1, -1, 1]

private theorem logWindow_eq_one {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    logWindow (Real.log x) = 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
  have hlog : Real.log x ≤ Real.log 2 := Real.log_le_log hx0 hx.2
  simp [logWindow, abs_of_nonneg hlog0, hlog]

theorem exp_pair_logs {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.exp (-Real.log x - Real.log y + Real.log z) = z / (x * y) := by
  rw [Real.exp_add, sub_eq_add_neg, Real.exp_add, Real.exp_neg,
    Real.exp_neg, Real.exp_log hx, Real.exp_log hy, Real.exp_log hz]
  field_simp

/-- Uniform separated integral for the ACTUAL paper radial Fourier transform.
Both rows and the source may vary independently within their dyadic boxes. -/
theorem radial_pair_log_separation (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ x y z : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
          y ∈ Set.Icc (1 : ℝ) 2 → z ∈ Set.Icc (1 : ℝ) 2 →
          paperRadialFourier W (R * z / (x * y)) =
            ∫ t : ℝ,
              (FourierBridge.logPhase t (-Real.log x) *
                FourierBridge.logPhase t (-Real.log y) *
                FourierBridge.logPhase t (Real.log z)) * b t) ∧
        Integrable (fun t : ℝ => ‖b t‖) volume ∧
        (1 + R) ^ A * (∫ t : ℝ, ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * ‖b t‖ ≤ C) := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨C, hC, hsep⟩ := paperRadialFourier_log_separation_envelope
    W (fun _ : Fin 3 => logWindow) pairSigns (fun _ => Real.log 2)
    (fun _ => hlog2)
    (by
      intro j y hy
      by_contra hn
      simp [logWindow, hn] at hy) A 0
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, heq, hi, hbound, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro x y z hx hy hz
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz.1
    have h := heq ![Real.log x, Real.log y, Real.log z]
    simp [Fin.prod_univ_three, Fin.sum_univ_three, pairSigns,
      logWindow_eq_one hx, logWindow_eq_one hy, logWindow_eq_one hz,
      one_mul] at h
    rw [show -Real.log x + -Real.log y + Real.log z =
      -Real.log x - Real.log y + Real.log z by ring,
      exp_pair_logs hx0 hy0 hz0] at h
    simpa only [mul_div_assoc] using h
  · simpa only [pow_zero, one_mul] using hi
  · simpa only [pow_zero, one_mul] using hbound
  · simpa only [pow_zero, mul_one] using hpoint

end
end Qrh.JointDetector
