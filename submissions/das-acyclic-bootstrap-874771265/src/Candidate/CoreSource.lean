/- Adapted for Subhanjan Das, AI-assisted with OpenAI Codex.
Computational definitions only; equivalence to the admitted predicate is proved separately.
Original Collet Apache-2.0 notice retained below. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.CoreVector
import Lean.Elab.Tactic.RCases
set_option autoImplicit false
namespace Das.QRH.CoreSource
structure Source where
 B : Rat
 L : Rat
 cap : Rat
 q : Rat
 allowance : Rat
 lowFee : Rat
 highFee : Rat
 deriving DecidableEq

def natural : Source := ⟨1,11243277/2500000,11/200,0,1/10^12,1/10^8,1/10^7⟩
def crossing (n low : Source) : Rat := (low.B-n.B)/(low.L-n.L)
def sourceDen (n low : Source) : Rat := 1-6*n.q*low.B/low.L
def sourceT (n : Source) (b : Rat) : Rat := n.B-n.L*(b-n.allowance)
def sourceA (n low : Source) (b : Rat) : Rat :=
 (n.q*(b+(sourceT n b-low.B)/low.L)+n.lowFee)/sourceDen n low
def sourceF (n low : Source) (b : Rat) : Rat := 1-6*sourceA n low b
def scalarGate (n low : Source) (b : Rat) (j : Fin 16) : Rat :=
 let a := sourceA n low b
 let t := sourceT n b
 let T := t+b
 let F := sourceF n low b
 let e := n.allowance
 let Lref := 49/100-(11243277/2500000)*b
 q![sourceDen n low,b-2*e,a,1/75-a,F-T/2-4*e,
 low.B*F-t-b-4*e,1-n.q*low.cap,
 n.lowFee-(n.q*low.B/low.L+n.q*low.cap+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(11243277/2500000)*b-10*e,
 5/6+(499/1000)*Lref-T-9*a-n.highFee,
 1-T-5*a-n.highFee,1-1/50-T-4*a-n.highFee,
 1-1/50-T-(9/2)*a-n.highFee,Lref-7*a-n.highFee] j

def weakCap (n low : Source) (b : Rat) : Rat :=
 low.cap*sourceF n low b-(low.B*sourceF n low b-sourceT n b)/low.L

def densityGate (n low : Source) (high : Option Source) (b ν : Rat) (j : Fin 9) : Rat :=
 let a := sourceA n low b
 let T := sourceT n b+b
 let S := b-2*n.allowance
 let F := sourceF n low b-n.allowance
 let fee := n.highFee
 let t := 15-6*ν
 let w := 5-6*ν
 let H := (a-ν*T)*t+(10-60*a)*ν
 let fixed := H+(ν*F/2-(1-ν)*b-fee)*t
 let core := H+((5/6)*F-(1-ν)*b-fee)*t-10*ν*F
 let tiny := H+(ν*(F-1/50)/2-(1-ν)*b-fee)*t-10*ν*(1/50)
 match high with
 | none =>
   let D2 := 115-54*ν
   let D3 := 185-138*ν
   q![H+3*ν*w*S-fee*t,
     H*D2+14*ν*w*S*t+2*ν*w*w*F-fee*t*D2,
     H*D3+16*ν*w*w*F-fee*t*D3,fixed,core,tiny,1,1,1] j
 | some h =>
   let D13 := h.L*t-10
   let D4 := 10+3*w
   let D23 := h.L*(10+3*w)-(10+2*w)
   q![H+3*ν*w*S-fee*t,
     H+(2*ν*w*S+ν*w*h.cap*F)-fee*t,
     H*D13+2*ν*w*(h.L-1)*S*t+ν*w*(h.B*t-10)*F-fee*t*D13,
     H*D4+ν*w*S*t+2*ν*w*w*F-fee*t*D4,
     H*D4+(2*ν*w*w+ν*w*h.cap*t)*F-fee*t*D4,
     H*D23+ν*w*(2*w*(h.L-1)+h.B*t-10)*F-fee*t*D23,
     fixed,core,tiny] j

/-- Coefficients of the unique cubic agreeing at 0, 1, -1 and 2. -/
def cubicCoeffs (f : Rat → Rat) : Fin 4 → Rat :=
 q![f 0,(-f 2+6*f 1-3*f 0-2*f (-1))/6,
 (f 1+f (-1)-2*f 0)/2,(f 2-3*f 1+3*f 0-f (-1))/6]
def cubicBernstein (f : Rat → Rat) (l r : Rat) (i : Fin 4) : Rat :=
 let c := cubicCoeffs f
 let a0 := c 0+c 1*l+c 2*l^2+c 3*l^3
 let a1 := (r-l)*(c 1+2*c 2*l+3*c 3*l^2)
 let a2 := (r-l)^2*(c 2+3*c 3*l)
 let a3 := (r-l)^3*c 3
 q![a0,a0+a1/3,a0+2*a1/3+a2/3,a0+a1+a2+a3] i

def SourceValid (n low : Source) (high : Option Source) : Prop :=
 0<n.B ∧ n.B≤1 ∧ 1<n.L ∧ 0≤n.cap ∧ n.cap<1 ∧
 1/2≤n.q ∧ n.q≤3/4 ∧ n.L<low.L ∧
 0≤crossing n low ∧ crossing n low≤n.cap ∧ crossing n low≤low.cap ∧
 (∀ h ∈ high, 22/23≤h.B ∧ h.B≤1 ∧ 1<h.L ∧ 0≤h.cap ∧ h.cap<1) ∧
 (∀ b ∈ [crossing n low,n.cap],
  (∀ j : Fin 16, 0<scalarGate n low b j) ∧ 0≤weakCap n low b ∧
  ∀ j : Fin 9, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate n low high b ν j) n.q (3/4) i)
instance (n low : Source) (high : Option Source) : Decidable (SourceValid n low high) := by
 unfold SourceValid
 infer_instance
end Das.QRH.CoreSource
