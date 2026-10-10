import QRH.AlgebraicRoot
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact geometry of the accepted manuscript. These are arithmetic lemmas,
not nonvanishing or moment estimates. -/
namespace QRH
noncomputable section

def theta : ℝ := (874957019421 / 1000000000000 : ℝ)

def tightTheta : ℝ := Algebraic.limitingTheta

theorem tightTheta_lt_theta : tightTheta < theta := by
  exact Algebraic.limitingTheta_upper.trans (by norm_num [theta])

theorem tightTheta_le_theta : tightTheta ≤ theta := tightTheta_lt_theta.le

def ell : ℝ := 11 / 3 - 4 * tightTheta
theorem ell_eq_root : ell = Algebraic.root := by
  unfold ell tightTheta Algebraic.limitingTheta
  ring

theorem ell_interval : ell ∈ Set.Icc (1/6:ℝ) (167/1000:ℝ) := by
  rw [ell_eq_root]
  exact Algebraic.root_narrow

theorem ell_cubic : Algebraic.cubic ell = 0 := by
  rw [ell_eq_root]
  exact Algebraic.root_spec.2

def kappa0 : ℝ := 2 * tightTheta - 1
def b : ℝ := -(3 * ell + 1) * (36 * ell ^ 2 - 75 * ell + 19) /
  (3 * (114 * ell ^ 2 - 159 * ell - 7))
def M : ℝ := 1 - ell
def lx : ℝ := (M - b) / 2
def ly : ℝ := (M + b) / 2
def h : ℝ := 1 - lx + ell
def zeta : ℝ := 1 / 100000000000000000000000000
def C (s : ℝ) : ℝ := s + lx / 2 - 1 + h / 6








theorem C_formula (s : ℝ) : C s = s - 2 / 3 - b / 6 := by
  dsimp [C, h, lx, M]
  ring



def kappa (B : ℝ) : ℝ := 2 * B - 1











end
end QRH
