import Mathlib.Tactic

noncomputable section

namespace OAI.SevenEighths.Target830

inductive SourcePlane where
  | A | C
  deriving DecidableEq

instance : Fintype SourcePlane := ⟨{.A, .C}, by intro P; cases P <;> simp⟩

def theta : ℝ := 87483/100000
def h : ℝ := 398511/500000
def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def dMinus : ℝ := h-3/2000
def dPlus : ℝ := h+1/10000000000
def kappaStar : ℝ := 2*theta-1
def kappa0 : ℝ := 93709/125000
def plainKappa : ℝ := 3/4
def slotClip : ℝ := 399999/10000000
def physicalSwitch : ℝ := 3/2000
def plainLower : ℝ := 81/200
def plainUpper : ℝ := 11/25
def widthLower : ℝ := 17/500
def widthUpper : ℝ := 1/25
def zeta : ℝ := 1/1000000
def sourceWidthMesh : ℝ := 1/100000000
def sourceDiscard : ℝ := 1/500000000
def frequencyAllowance : ℝ := 1/1000000000
def lowReserve : ℝ := 1/4000000
def highReserve : ℝ := 1/1000000
def highRawFee : ℝ := 1/10000000
def errorReserve : ℝ := 1/1000000

namespace SourcePlane

def B : SourcePlane → ℝ
  | .A => 9816147/10000000
  | .C => 3915977/4000000

def lambda : SourcePlane → ℝ
  | .A => 37961251/10000000
  | .C => 372765011/100000000

def q : SourcePlane → ℝ
  | .A => 6509/10000
  | .C => 6419/10000

def rootCutoff : SourcePlane → ℝ
  | .A => 117/25000
  | .C => 231/50000

def gap (P : SourcePlane) (b : ℝ) : ℝ := P.B-1+(6*kappa0-P.lambda)*b
def amp (P : SourcePlane) (b : ℝ) : ℝ :=
  P.q*P.gap b/(6*(kappa0-P.q))+lowReserve/(1-P.q/kappa0)
def total (P : SourcePlane) (b : ℝ) : ℝ :=
  P.B-(P.lambda-1)*(b-sourceWidthMesh)
def supplied (_P : SourcePlane) (b : ℝ) : ℝ := b-sourceWidthMesh-sourceDiscard
def frequency (P : SourcePlane) (b : ℝ) : ℝ :=
  (1-6*P.rootCutoff)*(1-6*P.amp b-frequencyAllowance)

theorem parameter_bounds (P : SourcePlane) :
    31/50 ≤ P.q ∧ P.q < 7/10 ∧ P.q < kappa0 ∧
    0 < P.rootCutoff ∧ P.rootCutoff ≤ 7/1000 ∧
    0 < P.lambda ∧ P.lambda < 6*kappa0 ∧ P.lambda < 9/2 := by
  cases P <;> norm_num [q,rootCutoff,lambda,kappa0]

end SourcePlane

def rho (delta : ℝ) : ℝ := 1-10*delta/(3*(5-2*delta))
def phi (delta : ℝ) : ℝ := delta*(5-6*delta)/(5-2*delta)
def capI (delta : ℝ) : ℝ := (1-zeta)*9*(5-6*delta)/(380-240*delta)
def capP (delta : ℝ) : ℝ := 4*capI delta/9
def commonGamma (delta : ℝ) : ℝ := delta-max (3/19) (4*rho delta-5/4)

theorem exact_geometry :
    ell=12551/75000 ∧ x=555487/1500000 ∧ y=693493/1500000 ∧
    dMinus=397761/500000 ∧ dPlus=7970220001/10000000000 ∧
    kappaStar=37483/50000 := by
  norm_num [ell,x,y,theta,h,dMinus,dPlus,kappaStar]

end OAI.SevenEighths.Target830

#print axioms OAI.SevenEighths.Target830.SourcePlane.parameter_bounds
#print axioms OAI.SevenEighths.Target830.exact_geometry
