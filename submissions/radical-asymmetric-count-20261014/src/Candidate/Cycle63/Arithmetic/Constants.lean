import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace Cycle63.Arithmetic

noncomputable section

def theta : ℝ := 8748559/10000000
def c : ℝ := 1251441/10000000
def h : ℝ := 7953177/10000000
def ell : ℝ := 1254323/7500000
def x : ℝ := 11157761/30000000
def y : ℝ := 13824947/30000000
def kappaStar : ℝ := 3748559/5000000
def dMinus : ℝ := 7948177/10000000
def dPlus : ℝ := 7953177001/10000000000
def d0 : ℝ := 1 / 200
def lambda : ℝ := 19312 / 4787
def B : ℝ := 142100527/143610000
def B0 : ℝ := 14200 / 14361
def q0 : ℝ := 17 / 25
def rho0 : ℝ := 103 / 273
def Ka : ℝ := 34 / 21
def alpha : ℝ := 1 / 400000
def t0 : ℝ := 1 / 1000

theorem theta_eq : theta = 1 - c := by norm_num [theta, c]
theorem ell_eq : ell = 11 / 3 - 4 * theta := by norm_num [ell, theta]
theorem x_eq : x = 1 + ell - h := by norm_num [x, ell, h]
theorem y_eq : y = h - 2 * ell := by norm_num [y, ell, h]
theorem kappaStar_eq : kappaStar = 2 * theta - 1 := by norm_num [kappaStar, theta]
theorem dMinus_eq : dMinus = h - 1 / 2000 := by norm_num [dMinus, h]
theorem dPlus_eq : dPlus = h + 1 / 10000000000 := by norm_num [dPlus, h]
theorem B_eq : B = B0 + 7 / 10000 := by norm_num [B, B0]

theorem ell_pos : 0 < ell := by norm_num [ell]
theorem ell_lt_x : ell < x := by norm_num [ell, x]
theorem x_lt_y : x < y := by norm_num [x, y]
theorem y_lt_two_x : y < 2 * x := by norm_num [y, x]
theorem y_lt_half : y < 1 / 2 := by norm_num [y]
theorem half_lt_h : 1 / 2 < h := by norm_num [h]
theorem h_lt_two_y : h < 2 * y := by norm_num [h, y]
theorem sixth_lt_ell : 1 / 6 < ell := by norm_num [ell]
theorem ell_lt_fifth : ell < 1 / 5 := by norm_num [ell]
theorem four_ell_lt_h : 4 * ell < h := by norm_num [ell, h]
theorem x_add_y : x + y = 1 - ell := by norm_num [x, y, ell]
theorem d0_pos : 0 < d0 := by norm_num [d0]
theorem half_lt_dMinus : 1 / 2 < dMinus := by norm_num [dMinus]
theorem dMinus_lt_h : dMinus < h := by norm_num [dMinus, h]
theorem h_lt_dPlus : h < dPlus := by norm_num [h, dPlus]
theorem dPlus_lt_one : dPlus < 1 := by norm_num [dPlus]
theorem kappaStar_mem : 7 / 10 ≤ kappaStar ∧ kappaStar ≤ 3 / 4 := by
  norm_num [kappaStar]
theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem lambda_pos : 0 < lambda := by norm_num [lambda]
theorem B_pos : 0 < B := by norm_num [B]

end

end Cycle63.Arithmetic
