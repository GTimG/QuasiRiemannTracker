import QRH.Geometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace QRH

/-- Continuous bound for the change from reference to dynamic plain capacity.
The moment estimates to which the capacities apply are separate obligations. -/
theorem dynamic_capacity_loss {κ₀ κ q m Δ : ℝ}
    (hk0 : (13 / 18 : ℝ) ≤ κ₀) (hk : (13 / 18 : ℝ) ≤ κ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 5 / 12) (hm0 : (1 / 3 : ℝ) ≤ m)
    (hm1 : m ≤ 1 / 2) (hd : 0 ≤ Δ) (heq : κ = κ₀ + 2 * Δ) :
    q * (1 - 2 * m) / 3 * (1 / κ₀ - 1 / κ) ≤ (30 / 169 : ℝ) * Δ := by
  have hk0p : 0 < κ₀ := by linarith
  have hkp : 0 < κ := by linarith
  have hdenp : 0 < 3 * κ₀ * κ := by positivity
  have hden : (169 / 108 : ℝ) ≤ 3 * κ₀ * κ := by
    have hh := mul_le_mul hk0 hk (by norm_num : (0 : ℝ) ≤ 13 / 18) hk0p.le
    nlinarith [hh]
  have hn : 2 * q * (1 - 2 * m) ≤ (5 / 18 : ℝ) := by
    have hh := mul_le_mul hq1 (show 1 - 2 * m ≤ (1 / 3 : ℝ) by linarith)
      (show 0 ≤ 1 - 2 * m by linarith) (by norm_num : (0 : ℝ) ≤ 5 / 12)
    nlinarith [hh]
  have hcoef : 2 * q * (1 - 2 * m) / (3 * κ₀ * κ) ≤ (30 / 169 : ℝ) := by
    apply (div_le_iff₀ hdenp).mpr
    nlinarith
  calc
    q * (1 - 2 * m) / 3 * (1 / κ₀ - 1 / κ) =
        (2 * q * (1 - 2 * m) / (3 * κ₀ * κ)) * Δ := by
      field_simp
      rw [heq]
      ring
    _ ≤ (30 / 169 : ℝ) * Δ := mul_le_mul_of_nonneg_right hcoef hd

theorem dynamic_capacity_strict_slack {Δ : ℝ} (hd : 0 < Δ) :
    (30 / 169 : ℝ) * Δ < Δ / 4 := by linarith

end QRH
