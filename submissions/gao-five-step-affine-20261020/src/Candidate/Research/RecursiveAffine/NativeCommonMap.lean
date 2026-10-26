/- Copyright (c) 2026 Hailey Collet; regional source composition (c) 2026
Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.SecondLowGeometry
import Candidate.Research.RecursiveAffine.NativePhysicalBridge

set_option autoImplicit false
set_option maxHeartbeats 10000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonLinearNormalization
open CenteredMomentDivisorAllocation CenteredMomentAmplificationChildInput
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle153SourceReturn
open Cycle63Moment.LowBranch

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- The second common allocation is the actual one selected by the physical
common-source index. The first allocation, conductor and dictionary do not
change. -/
def commonContinuationChain (s : Input alpha) (q : Chain s)
    (chi : Character) (t : ℝ)
    (B : actualAllocations (withHeight q.first chi t).pools q.E₂) : Chain s :=
  {q with B₂:=B}

/-- Literal transport of the native live-row geometry to the selected
second common allocation. Nonzero common scalar supplies the missing
frozen coefficient; the ray, inactive set and common data remain the same. -/
def commonContinuationGeometry {s : Input alpha} {q : Chain s}
    {Z Mrow amp omega xi b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega xi b N)
    (chi : Character) (t : ℝ)
    (B : actualAllocations (withHeight q.first chi t).pools q.E₂)
    (hn : commonScalar (withHeight q.first chi t) q.E₂ q.R₂ B ≠ 0) :
    LiveMainGeometry s (commonContinuationChain s q chi t B) Z Mrow amp omega xi b N :=
  { reflected:=g.reflected, C₀:=g.C₀,D₀:=g.D₀,hC₀:=g.hC₀,hD₀:=g.hD₀,
    heq₀:=g.heq₀,selected:=g.selected,E₀:=g.E₀,hmod:=g.hmod,
    δ:=g.δ,reserve:=g.reserve,homega:=g.homega,datum:=g.datum,
    parent:=g.parent,row:=g.row,radius_eq:=g.radius_eq,label:=g.label,
    first_nonzero:=g.first_nonzero,second_nonzero:=right_ne_zero_of_mul hn }

@[simp] theorem commonContinuationChain_final (s : Input alpha) (q : Chain s)
    (chi : Character) (t : ℝ)
    (B : actualAllocations (withHeight q.first chi t).pools q.E₂) :
    (commonContinuationChain s q chi t B).final chi t=
      commonData (withHeight q.first chi t) q.E₂ q.R₂ B := rfl

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.commonContinuationGeometry
