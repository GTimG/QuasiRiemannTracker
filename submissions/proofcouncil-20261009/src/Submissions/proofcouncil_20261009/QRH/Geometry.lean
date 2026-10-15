import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact geometry of the accepted manuscript. These are arithmetic lemmas,
not nonvanishing or moment estimates. -/
namespace QRH
noncomputable section

def theta : ℝ := (874957019421 / 1000000000000 : ℝ)
def ell : ℝ := 11 / 3 - 4 * theta
def kappa0 : ℝ := 2 * theta - 1
def b : ℝ := -(3 * ell + 1) * (36 * ell ^ 2 - 75 * ell + 19) /
  (3 * (114 * ell ^ 2 - 159 * ell - 7))
def M : ℝ := 1 - ell
def lx : ℝ := (M - b) / 2
def ly : ℝ := (M + b) / 2
def h : ℝ := 1 - lx + ell
def zeta : ℝ := 1 / 100000000000000
def C (s : ℝ) : ℝ := s + lx / 2 - 1 + h / 6

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7 / 8 : ℝ) := by norm_num [theta]
theorem improvement : (3499999 / 4000000 : ℝ) - theta =
    42730579 / 1000000000000 := by norm_num [theta]
theorem ell_value : ell = (125128941737 / 750000000000 : ℝ) := by norm_num [ell, theta]
theorem kappa0_value : kappa0 = (374957019421 / 500000000000 : ℝ) := by
  norm_num [kappa0, theta]
theorem geometry_identities :
    theta = 1 - h / 6 + b / 12 ∧ theta = 11 / 12 - ell / 4 ∧
    kappa0 = 5 / 6 - ell / 2 ∧ C theta = lx / 2 + b / 12 := by
  dsimp [C, h, lx, M, ell, kappa0]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem C_formula (s : ℝ) : C s = s - 2 / 3 - b / 6 := by
  dsimp [C, h, lx, M]
  ring

theorem geometry_ledger :
    (1 / 6 : ℝ) < ell ∧ ell < 167 / 1000 ∧ ell < 1 / 5 ∧
    (123 / 1000 : ℝ) < b ∧ b < 124 / 1000 ∧
    M - 2 * ell > 49 / 100 ∧ lx - ell > 9 / 50 ∧
    ly - ell - 11 * b / 6 > 2 / 25 ∧
    (35 / 100 : ℝ) < lx ∧ lx < 36 / 100 ∧
    (47 / 100 : ℝ) < ly ∧ ly < 49 / 100 ∧
    (81 / 100 : ℝ) < h ∧ h < 82 / 100 ∧
    ell / (h + zeta) > 1 / 5 ∧
    (43 / 50 : ℝ) < theta ∧ theta < 3499999 / 4000000 ∧
    (13 / 18 : ℝ) < kappa0 ∧ (37 / 50 : ℝ) < kappa0 ∧ kappa0 < 3 / 4 := by
  norm_num [ell, theta, b, M, lx, ly, h, zeta, kappa0]

def kappa (B : ℝ) : ℝ := 2 * B - 1

theorem dynamic_kappa {B : ℝ} (hB : theta < B) (hB1 : B ≤ 1) :
    13 / 18 < kappa B ∧ kappa B ≤ 1 ∧
    kappa B = kappa0 + 2 * (B - theta) ∧ B = (1 + kappa B) / 2 := by
  have hk0 : (13 / 18 : ℝ) < kappa0 := by norm_num [kappa0, theta]
  dsimp [kappa, kappa0] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> ring

/-- The old lower endpoint really fails in part of the required domain. -/
theorem old_moment_range_insufficient :
    ∃ B : ℝ, theta < B ∧ B < 7 / 8 ∧ kappa B < 3 / 4 := by
  refine ⟨(theta + 7 / 8) / 2, ?_⟩
  norm_num [theta, kappa]

/-- Centering margin in Appendix `app:plain`, including κ=13/18. -/
theorem plain_centering {κ z width total ξ reflected : ℝ}
    (hκ : (13 / 18 : ℝ) ≤ κ) (hz : 0 ≤ z)
    (hlarge : 5 * width / 6 < total)
    (hcap : total + (6 * κ - 1) * z ≤ width)
    (href : reflected ≤ 3 * width / 2 - total + 2 * z + ξ) :
    z < width / 20 ∧ reflected < 23 * width / 30 + ξ ∧
    reflected + (6 * κ - 1) * z < 14 * width / 15 + ξ := by
  have hkz : (10 / 3 : ℝ) * z ≤ (6 * κ - 1) * z :=
    mul_le_mul_of_nonneg_right (by linarith) hz
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The positive slot allowance alone gives the induction terminal bounds. -/
theorem plain_slot_budget {κ z n₁ n₂ width : ℝ}
    (hκ : (13 / 18 : ℝ) ≤ κ) (hz : 0 ≤ z)
    (h₁ : 0 ≤ n₁) (h₂ : 0 ≤ n₂) (hcap : n₁ + n₂ + 6 * κ * z ≤ width) :
    z ≤ 3 * width / 13 ∧ κ * z ≤ width / 6 := by
  have hkz := mul_le_mul_of_nonneg_right hκ hz
  constructor <;> nlinarith

/-- The continuous low-energy exponent inequality, manuscript `lem:energy`.
This is the real linear program, not the reflected analytic energy estimate. -/
theorem low_energy {d l r A N S G z O v t e H vartheta : ℝ}
    (hd : 0 ≤ d) (hdl : d ≤ l) (hl : l ≤ 1 / 5) (hr : 0 ≤ r)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hS : 0 ≤ S) (hG : 0 ≤ G) (hz : 0 ≤ z)
    (hO : -r ≤ O) (hv : -r ≤ v) (ht : -r ≤ t) (he : -r ≤ e)
    (hvartheta : |vartheta| ≤ r)
    (hH : H ≤ (1 - l - 2 * d) - O + r) (hAO : 2 * A ≤ O + r)
    (hNA : N ≤ A) (hzl : z ≤ l - d)
    (hy : v + 3 * t + e ≤ 2 * H + 2 * A + 2 * z - 1 - (l - d) - vartheta - N - 3 * G + r) :
    O / 2 + max H (v + t) - S - G + z - min v (min z ((v + z) / 3)) - t - 2 * e / 3 -
      max (2 * H + 2 * A + 2 * z - 1 - (l - d) - vartheta - N - 3 * G -
        (v + 3 * t + e)) 0 / 2 ≤
      (1 - l - 2 * d) + max (5 * l + d - 1) 0 / 4 + 11 * r := by
  obtain ⟨hvlo, hvhi⟩ := abs_le.mp hvartheta
  simp only [max_def, min_def]
  split_ifs <;> linarith

end
end QRH
