/- Repeated marks: fork of Collet's generic return module Schedule (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Geometry and finite scalar certificates for the reusable physical return. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.TransportGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return.GenericArithmetic
open QRH.Record1252270103Return
noncomputable section
variable [Geometry.Parameters]
abbrev theta:ℝ := Geometry.theta
abbrev h:ℝ := Geometry.h
abbrev ell:ℝ := Geometry.ell
abbrev x:ℝ := Geometry.x
abbrev y:ℝ := Geometry.y
def kappa:ℝ := 2*theta-1
def d0:ℝ := 1/200
abbrev dp:ℝ := Geometry.dPlus
def cap:ℝ := 9/200
def plainLower:ℝ := 2/5
def freeShift:ℝ := 1/400
def rowFee:ℝ := 1/1000000000

def Ebase (d C δ p:ℝ):ℝ :=
 1/2+13*h/75-y/2-ell/2-9*d/100+δ/2+δ*p*(ell-C/2)
def rowAt (bs:List Branch) (κ d C δ p:ℝ):ℝ :=
 Ebase d C δ p+3*d*QRH.Record1252270103Return.envelope bs κ δ p/4
def oldCapacityAt (κ d:ℝ):ℝ := min d (2*y-d)/(6*κ)

class PhysicalSchedule [scheme:CountScheme] where
 dMinus:ℝ
 physicalB:ℝ
 physicalLambda:ℝ
 dMinus_lower:3/4<dMinus
 dMinus_before_top:dMinus≤dp
 y_before_switch:y<dMinus
 switch_before_twoy:dMinus<2*y
 lambda_bounds:2≤physicalLambda ∧ physicalLambda≤9/2
 B_bounds:0<physicalB ∧ physicalB≤1
 small_plain_global:0≤1-physicalB/2-(9/2-physicalLambda/2)*cap
 prime_supply:1/5<ell/dp
 incumbent:kappa≤scheme.naturalκ
 old_rows:∀{d δ p:ℝ},d∈Set.Icc d0 dMinus → δ∈Set.Icc 0 (3/4) → p∈Set.Icc 0 (1/2) →
  rowAt GenericCount.admittedBranches kappa d (oldCapacityAt kappa d) δ p≤theta-rowFee
 new_rows:∀{d δ p:ℝ},d∈Set.Icc dMinus dp → δ∈Set.Icc 0 (3/4) → p∈Set.Icc 0 (1/2) →
  rowAt GenericCount.admittedBranches kappa d
   (min (cap*d) ((2*y-(2-physicalB)*d)/physicalLambda)) δ p≤theta-rowFee

variable [CountScheme] [PhysicalSchedule]
abbrev dm:ℝ := PhysicalSchedule.dMinus
abbrev physicalB:ℝ := PhysicalSchedule.physicalB
abbrev physicalLambda:ℝ := PhysicalSchedule.physicalLambda
def newCapacity (d:ℝ):ℝ := min (cap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
def oldExponent (bs:List Branch) (d δ p:ℝ):ℝ := rowAt bs kappa d (oldCapacityAt kappa d) δ p
def newExponent (bs:List Branch) (d δ p:ℝ):ℝ := rowAt bs kappa d (newCapacity d) δ p
def newExponentAt (bs:List Branch) (κ d δ p:ℝ):ℝ := rowAt bs κ d (newCapacity d) δ p
def oldExponentAt (bs:List Branch) (κ d δ p:ℝ):ℝ := rowAt bs κ d (oldCapacityAt κ d) δ p
end
end QRH.RepeatedMarks.Return.GenericArithmetic
