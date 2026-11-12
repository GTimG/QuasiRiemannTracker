/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.ProfileWide
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.CommonMeasure

/-!
# Inverse.Restore.TauMoment — the row moment of a separated integral

**`tau_moment_le`**: if `∑_y ‖F y τ‖² ≤ A (1+|τ|)^(2 deg)` for every separation frequency `τ`,
then `∑_y ‖∫ b(τ) F y τ dτ‖² ≤ (∫ ‖b‖ (1+|τ|)^deg)² · A` (baseline `common_measure_energy` with
the weight `b · (1+|τ|)^deg`; template `Select/Separate.selected_energy_bound`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped BigOperators SchwartzMap
open MeasureTheory OAI OAI.SevenEighths.InverseMoment

theorem tau_moment_le {Row : Type*} (rows : Finset Row) (b : 𝓢(ℝ, ℂ)) (F : Row → ℝ → ℂ)
    (deg : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hint : ∀ y ∈ rows, Integrable (fun τ => b τ * F y τ))
    (hbound : ∀ τ : ℝ, ∑ y ∈ rows, ‖F y τ‖^2 ≤ A * ((1 + ‖τ‖)^deg)^2) :
    ∑ y ∈ rows, ‖∫ τ, b τ * F y τ‖^2 ≤ (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^deg)^2 * A := by
  set hw : ℝ → ℝ := fun t => (1 + ‖t‖)^deg with hhw
  have hw0 : ∀ t, 0 < hw t := fun t => by simp only [hhw]; positivity
  let b' : ℝ → ℂ := fun t => b t * ((hw t : ℝ) : ℂ)
  let φ : ↥rows → ℝ → ℂ := fun y t => F y.1 t / ((hw t : ℝ) : ℂ)
  have hbφ : ∀ (y : ↥rows) t, b' t * φ y t = b t * F y.1 t := by
    intro y t
    have hn : ((hw t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hw0 t).ne'
    simp only [b', φ]
    field_simp
  have hint' : ∀ y : ↥rows, Integrable (fun t => b' t * φ y t) := by
    intro y
    simp only [hbφ]
    exact hint y.1 y.2
  have hb' : Integrable (fun t => ‖b' t‖) := by
    refine (schwartz_weight_integrable b deg).congr ?_
    filter_upwards with t
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, hhw]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |t|)^deg)]
  have hbound' : ∀ t, (∑ y : ↥rows, ‖φ y t‖^2) ≤ A := by
    intro t
    have h1 : ∀ y : ↥rows, ‖φ y t‖^2 = ‖F y.1 t‖^2 / (hw t)^2 := by
      intro y
      simp only [φ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw0 t), div_pow]
    simp only [h1]
    rw [Finset.sum_coe_sort rows (fun y => ‖F y t‖^2 / (hw t)^2), ← Finset.sum_div,
      div_le_iff₀ (by have := hw0 t; positivity)]
    exact hbound t
  have hmain := common_measure_energy volume b' φ A hA hb' hint' hbound'
  have hlhs : ∑ y ∈ rows, ‖∫ τ, b τ * F y τ‖^2 = ∑ y : ↥rows, ‖∫ t, b' t * φ y t‖^2 := by
    rw [← Finset.sum_coe_sort rows (fun y => ‖∫ τ, b τ * F y τ‖^2)]
    apply Finset.sum_congr rfl
    intro y _
    simp only [hbφ]
  have hb'n : (∫ t, ‖b' t‖) = ∫ t, ‖b t‖ * (1 + ‖t‖)^deg := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, hhw]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |t|)^deg)]
  rw [hlhs]
  refine hmain.trans (le_of_eq ?_)
  rw [hb'n]
  ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.tau_moment_le
