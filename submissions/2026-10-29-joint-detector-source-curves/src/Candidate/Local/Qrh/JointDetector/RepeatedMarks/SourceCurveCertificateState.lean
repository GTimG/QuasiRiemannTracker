/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveTheorem

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveCertificate
noncomputable section
set_option autoImplicit false

/-- Real scalar state of a polynomial curve at one parameter value. -/
structure State where
  q : ℝ
  y : ℝ
  k : ℝ
  a : ℝ
  eps : ℝ
  cap : ℝ

namespace State
def D (p : State) : ℝ := 6*p.q^2*p.k
def S (p : State) : ℝ := p.q*(1+p.q)*p.k-p.y
def B (p : State) : ℝ := (1+p.q)/(6*p.q*p.y)
def L (p : State) : ℝ := 1/p.y
def s (p : State) : ℝ := p.S/p.D
def n (p : State) : ℝ := p.q-p.eps
def r (p : State) : ℝ := p.a/p.q

def common (p : State) : Fin 20→ℝ :=
 ![p.n-2/5,3/4-p.q,p.y,1-p.y,p.k,p.D,6*p.q*p.y-(1+p.q),
   p.S,p.cap*p.D-p.S,p.D-1,1+p.q-6*p.q*p.cap,p.D-1-2*p.S,
   6*p.q*p.y*(1-2*p.cap)-(1+p.q)+6*p.q*p.cap,
   31/20*p.D-3/2-5/2*p.S,
   6*p.q*p.y*(31/20-5/2*p.cap)-3/2*(1+p.q-6*p.q*p.cap),
   p.D-1-p.S,6*p.q*p.y*(1-p.cap)-(1+p.q)+6*p.q*p.cap,
   1/3-2*p.cap,(1+p.q)-9/10*(6*p.q*p.y),1-3/2*p.y]

def derivative (p : State) (ν : ℝ) : ℝ :=
  ν*(-p.D*p.q+p.q/2+2*p.S*p.a)+p.q*(5/12-5/3*p.S)
def repeated (p : State) (ν : ℝ) : ℝ :=
  (p.D*p.q-p.S*p.a)*(5/3*p.q-p.a*ν)+p.q^2*ν-5/2*p.q^2+p.a*p.q*ν/2+5/12*p.a*p.q
def selected (p : State) (ν : ℝ) : ℝ :=
  (2*p.q+p.a)*p.D*p.q-3*p.q*(p.q+p.S*p.a)+
    ν*((p.q+2*p.a)*(p.q+p.S*p.a)-3*p.a*p.D*p.q)
def combined (p : State) : Fin 10→ℝ :=
 ![p.n-50001/100000,p.a,p.q-p.a,p.a*p.n-500001/1000000*p.q,
   -p.derivative p.n,p.repeated p.n,p.selected p.n,
   -p.derivative (3/4),p.repeated (3/4),p.selected (3/4)]
def pureDerivative (p : State) (ν : ℝ) : ℝ :=
  ν*(-p.D+1/2)-5/3*p.S+5/12+2*p.S*ν
def pureRepeated (p : State) (ν : ℝ) : ℝ :=
  (3/2+p.S-p.D)*ν+5/3*(p.D-p.S)-25/12
def pure (p : State) : Fin 4→ℝ :=
 ![-p.pureDerivative p.n,p.pureRepeated p.n,-p.pureDerivative (3/4),p.pureRepeated (3/4)]
end State
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveCertificate
