import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact geometry of the accepted manuscript. These are arithmetic lemmas,
not nonvanishing or moment estimates. -/
namespace QRH
noncomputable section

def theta : ℝ := (874957019421 / 1000000000000 : ℝ)

def tightTheta : ℝ := (874957019420098946128604623 / 1000000000000000000000000000 : ℝ)

theorem tightTheta_lt_theta : tightTheta < theta := by
  norm_num [tightTheta, theta]

theorem tightTheta_le_theta : tightTheta ≤ theta := tightTheta_lt_theta.le

def ell : ℝ := 11 / 3 - 4 * tightTheta
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
