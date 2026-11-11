import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace QRH.PositiveGap.Return
noncomputable section
class TargetC where
  c : ℝ
  c_lo : (1266180 / 10000000 : ℝ) ≤ c
  c_quad : (852 * c - 75) ^ 2 < 1081
variable [TargetC]
def c : ℝ := TargetC.c
def gap : ℝ := 1081 - (852 * c - 75) ^ 2
def eps : ℝ := gap / 10000000000
def h : ℝ := 2 * (5028 * c - 199) / 1081
def physicalB : ℝ := 1 - eps
def physicalLambda : ℝ := 2 + 10 * eps
def physicalCap : ℝ := (3 / 25 : ℝ)
def countCB : ℝ := 1 - eps
def countCL : ℝ := 2 + 10 * eps
def countCap : ℝ := (671447 / 5000000 : ℝ)
def naturalK : ℝ := (9 / 2 : ℝ)
def sMinus : ℝ := (27 / 1000 : ℝ)
def mMinus : ℝ := (3 / 10 : ℝ)
def theta : ℝ := 1 - c
def ell : ℝ := 4 * c - 1 / 3
def x : ℝ := 1 + ell - h
def y : ℝ := h - 2 * ell
def kappa : ℝ := 1 - 2 * c
def numeratorCap : ℝ := (3 / 40 : ℝ)
def dm : ℝ := (19 / 25 : ℝ)
def dp : ℝ := h + eps
def d0 : ℝ := 1 / 200
def oldCapacity (d : ℝ) : ℝ := min d (2 * y - d) / (6 * kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap * d) ((2 * y - (2 - physicalB) * d) / physicalLambda)
def reserve : ℝ := eps
inductive Edge | oldSmall | oldSwitch | newSwitch | newTop
  deriving DecidableEq
def edgeD : Edge → ℝ
  | .oldSmall => d0
  | .oldSwitch | .newSwitch => dm
  | .newTop => dp
def edgeC (e : Edge) : ℝ := match e with
  | .oldSmall | .oldSwitch => oldCapacity (edgeD e)
  | .newSwitch | .newTop => newCapacity (edgeD e)
theorem c_lo : (1266180 / 10000000 : ℝ) ≤ c := TargetC.c_lo
theorem c_quad : (852 * c - 75) ^ 2 < 1081 := TargetC.c_quad
theorem c_hi : c ≤ 1266181 / 10000000 := by
  have hq := c_quad
  have hsq : 0 ≤ (852 * c - 75 - 82196553 / 2500000) ^ 2 := sq_nonneg _
  nlinarith
theorem gap_pos : 0 < gap := by
  unfold gap
  linarith [c_quad]
theorem gap_le : gap ≤ 1 / 500 := by
  unfold gap
  have hlo := c_lo
  have hsq : 0 ≤ (852 * c - 75 - 4109817 / 125000) ^ 2 := sq_nonneg _
  nlinarith
theorem eps_pos : 0 < eps := by
  unfold eps
  linarith [gap_pos]
theorem eps_le : eps ≤ 1 / 1000000000 := by
  unfold eps
  linarith [gap_le]
theorem theta_value : theta = 1 - c := rfl
theorem geometry_mellin : theta - (4 + y - x) / 6 = x / 2 + (y - x) / 12 := by
  unfold theta x y ell
  linarith
end
end QRH.PositiveGap.Return
