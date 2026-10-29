/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
noncomputable section

-- Supplemental certificate SHA-256: bafb7176290f6e85eb33a160d142e111fff97004a50c49eaf51d2d5feb3709c9
def theta : ℝ := (87393871/100000000:ℝ)
def h : ℝ := (10063329/12500000:ℝ)
def physicalB : ℝ := (4934995154607585173877/5000000000000000000000:ℝ)
def physicalLambda : ℝ := (57755268577/25000000000:ℝ)
def physicalCap : ℝ := (31/500:ℝ)
def countCB : ℝ := (38904970431209593637883/40000000000000000000000:ℝ)
def countCL : ℝ := (424191237967/200000000000:ℝ)
def countCap : ℝ := (9999/100000:ℝ)
def naturalK : ℝ := (9/2:ℝ)
def sMinus : ℝ := (3/100:ℝ)
def mMinus : ℝ := (377/1000:ℝ)
def numeratorCap : ℝ := (3/50:ℝ)
def dm : ℝ := (19/25:ℝ)
def d0 : ℝ := (1/200:ℝ)
def reserve : ℝ := (1/100000000:ℝ)
def c : ℝ := 1-theta
def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 2*theta-1
def dp : ℝ := h+1/10000000000
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
end Qrh.JointDetector.PointwiseReturn
