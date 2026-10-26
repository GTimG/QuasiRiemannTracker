import Submissions.hailey_collet_1252270103.Cycle61.Arithmetic.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cycle61.Arithmetic

noncomputable section

def g (b : ℝ) : ℝ := B - 1 + (9 / 2 - lambda) * b
def amp (b : ℝ) : ℝ := Ka * g b + alpha
-- The lower edge is one mesh step below the cell's upper edge.
def totalA (b : ℝ) : ℝ := B - (lambda - 1) * (b - 1 / 100000)
def cellUpper (j : ℕ) : ℝ := 17 / 500 + (j : ℝ) / 100000

theorem cellUpper_bounds {j : ℕ} (hj1 : 1 ≤ j) (hj600 : j ≤ 600) :
    3401 / 100000 ≤ cellUpper j ∧ cellUpper j ≤ 1 / 25 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have h600 : (j : ℝ) ≤ (600 : ℝ) := by exact_mod_cast hj600
  constructor <;> unfold cellUpper <;> linarith

theorem g_bounds {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    2653291 / 574440000 ≤ g b ∧ g b ≤ 7097611 / 957400000 := by
  constructor <;> norm_num [g, B, lambda] at * <;> linarith

theorem g_pos {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    0 < g b := by
  have hg := (g_bounds hb).1
  linarith

theorem amp_bounds {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    902420521 / 120632400000 ≤ amp b ∧ amp b ≤ 289458497 / 24126480000 := by
  constructor <;> norm_num [amp, g, Ka, alpha, B, lambda] at * <;> linarith

theorem totalA_upper {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    totalA b ≤ 1271830639 / 1436100000 := by
  norm_num [totalA, B, lambda] at *
  linarith

theorem amp_pos {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    0 < amp b := by
  have ha := (amp_bounds hb).1
  linarith

theorem low_reserve (b : ℝ) :
    amp b * (1 - 4 * q0 / 3) - (2 * q0 / 9) * g b = 7 / 30000000 := by
  norm_num [amp, g, Ka, alpha, B, lambda, q0]
  ring

theorem high_slope_cancellation :
    q0 * (lambda - 1) = Ka * (5 - 6 * rho0) * (9 / 2 - lambda) := by
  norm_num [q0, lambda, Ka, rho0]

theorem high_reserve (b : ℝ) :
    1 - rho0 - q0 * totalA b - amp b * (5 - 6 * rho0) =
      720486667 / 30493190000000 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda, q0, rho0]
  ring

theorem first_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    530959781 / 482529600000 ≤ amp b / 4 - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem sixth_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    11360006033 / 482529600000 ≤ 13 * amp b / 4 - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem seventh_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    3516816899 / 120632400000 ≤ 4 * amp b - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem second_zero_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    8754683599 / 120632400000 ≤ 1 - totalA b - 5 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem main_fixed_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    127361803 / 1507905000 ≤ 1 - totalA b - 4 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem error_fixed_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    988504553 / 40210800000 ≤ 1 - totalA b - 9 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem support_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    572201503 / 3446640000 ≤ 1 / 4 - 7 * amp b := by
  have ha := (amp_bounds hb).2
  linarith

theorem high_derivative_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    4397519373071 / 15608701631250 ≤
      50 * (1 - 6 * amp b) / (3 * (5 - 2 * q0) ^ 2) - totalA b := by
  have ha := (amp_bounds hb).2
  have hA := totalA_upper hb
  norm_num [q0] at *
  linarith

theorem cell_terminal_reserves {j : ℕ} (hj1 : 1 ≤ j) (hj600 : j ≤ 600) :
    0 < amp (cellUpper j) * (1 - 4 * q0 / 3) - (2 * q0 / 9) * g (cellUpper j) ∧
    0 < 1 - rho0 - q0 * totalA (cellUpper j) - amp (cellUpper j) * (5 - 6 * rho0) ∧
    0 < amp (cellUpper j) / 4 - g (cellUpper j) / 6 ∧
    0 < 13 * amp (cellUpper j) / 4 - g (cellUpper j) / 6 ∧
    0 < 4 * amp (cellUpper j) - g (cellUpper j) / 6 ∧
    0 < 1 - totalA (cellUpper j) - 5 * amp (cellUpper j) ∧
    0 < 1 - totalA (cellUpper j) - 4 * amp (cellUpper j) ∧
    0 < 1 - totalA (cellUpper j) - 9 * amp (cellUpper j) := by
  have hb := cellUpper_bounds hj1 hj600
  have hl := low_reserve (cellUpper j)
  have hh := high_reserve (cellUpper j)
  have h1 := first_error_reserve hb
  have h6 := sixth_error_reserve hb
  have h7 := seventh_error_reserve hb
  have hz := second_zero_reserve hb
  have hm := main_fixed_reserve hb
  have he := error_fixed_reserve hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem comparison_budget :
    (1 : ℝ) / 4 + 1 / 2 + (9 / 2) * (1 / 25) = 93 / 100 := by norm_num

theorem small_slot_complement :
    (2 : ℝ) * (264 / 625) + (9 / 2) * (17 / 500) = 1 - 11 / 5000 := by norm_num

theorem small_plain_complement :
    (41 : ℝ) / 100 + 264 / 625 + (9 / 2) * (37 / 1000) =
      1 - 11 / 10000 := by norm_num

theorem supply_lower :
    ell / dPlus - 4 / 21 = 44784748 / 2223053273 := by norm_num [ell, dPlus]

theorem supply_half :
    2 * ell - 1 / 3 = 139 / 125000 := by norm_num [ell]

theorem supply_four :
    4 * ell - y = 1046942013 / 5000000000 := by norm_num [ell, y]

theorem lower_row_reserve :
    theta - (7 / 8 - 49 * h / 150 + 7 * ell / 8 + 33 * d0 / 50) =
      82198036363 / 750000000000 := by norm_num [theta, h, ell, d0]

theorem floor_reserve :
    theta - (51 / 100 + h / 3 + 51 * ell / 100) =
      223923613 / 15000000000 := by norm_num [theta, h, ell]

theorem new_feedback_bound :
    5 * dPlus / 288 = 317579039 / 23040000000 ∧
      5 * dPlus / 288 < 1 / 50 := by norm_num [dPlus]

theorem old_feedback_bound : (695 : ℝ) / 14112 < 1 / 8 := by norm_num

theorem endpoint_extension_saving :
    (1 : ℝ) / 1000000 - 2 * (dPlus - h) = 4999 / 5000000000 := by
  norm_num [dPlus, h]

theorem principal_y_reserve :
    y / 20 - (1 + h) / 1000 - 1 / 4000 =
      313967484089 / 15000000000000 := by norm_num [y, h]

theorem principal_h_reserve :
    h / 600 - 1 / 1000 - 1 / 4000 =
      219737987 / 3000000000000 := by norm_num [h]

end

end Cycle61.Arithmetic

