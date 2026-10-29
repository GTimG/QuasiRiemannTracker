/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.DirectRoundedReturn
open QRH.Record1252270103Return
noncomputable section

-- Supplemental certificate SHA-256: 989641f707939379a73465925e46d717071e6e6d1da8ee4ae0c56a1f4ee8215e
def theta : ℝ := (4369178514865427/5000000000000000:ℝ)
def targetTheta : ℝ := (4369178514865427/5000000000000000:ℝ)
def h : ℝ := (811809573457442315654677/1000000000000000000000000:ℝ)
def physicalB : ℝ := (132365500000000000000000000000000000/134691681706757286391944389662954587:ℝ)
def physicalLambda : ℝ := (1000000000000000000000000000000/457834420624410799685731440459:ℝ)
def physicalCap : ℝ := (9999/100000:ℝ)
def countCB : ℝ := (755433010311/800000000000:ℝ)
def countCL : ℝ := (499999854189139951396678196647534309/291621720097206643606704931382000000:ℝ)
def countCap : ℝ := (10049/100000:ℝ)
def naturalK : ℝ := (9/2:ℝ)
def sMinus : ℝ := (3/100:ℝ)
def mMinus : ℝ := (377/1000:ℝ)
def numeratorCap : ℝ := (13/200:ℝ)
def dm : ℝ := (19/25:ℝ)
def d0 : ℝ := (1/200:ℝ)
def reserve : ℝ := (1/10000000000000000000000:ℝ)
def c : ℝ := 1-theta
def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 2*theta-1
def dp : ℝ := h+1/10000000000000000000000
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
inductive Edge | oldSmall | oldSwitch | newSwitch | newTop
  deriving DecidableEq
def edgeD : Edge → ℝ
  | .oldSmall => d0
  | .oldSwitch | .newSwitch => dm
  | .newTop => dp
def edgeC (e : Edge) : ℝ := match e with
  | .oldSmall | .oldSwitch => oldCapacity (edgeD e)
  | .newSwitch | .newTop => newCapacity (edgeD e)

end
end Qrh.JointDetector.DirectRoundedReturn
