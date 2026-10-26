/- Literal native common witnesses for the complete selected physical family.
Copyright (c)2026 Zhongpai Gao. Native source choices by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalActual
import Candidate.Research.RecursiveAffine.NativeSelectedForest
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation CenteredMomentSecondCanonical CenteredMomentFirstDiscardedEnergy
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle153RegionalLow Cycle153CanonicalLow
variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable (reflected second : Bool)(s : Input alpha)(R seed : Ideal O)
variable (Z Mrow amp xi reserve b firstHeight : ℝ)(budget : ℕ)(hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight budget
  hZ key hz1 hz2 firstIndex
local notation "datum"=>fun r : Rows=>geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b
  firstHeight budget hZ key (firstIndex r.val.1) hz1 hz2 r.val.2

/-- Genuine source data chosen once from every ORIGINAL nonzero block,
before ray, buffer, residual shell, or continuing source selection.
The witness carries no source-energy or recursive capacity estimate. -/
structure CanonicalSelectedFamily where
  allocation : (r : Rows)→actualAllocations (datum r).input.pools
    (if second then (datum r).D else (datum r).C)
  row : (r : Rows)→secondLiveRows (fun _:Unit=>(datum r).block)
  frozen : ∀r,frozenCoefficient (allocation r).val (if second then (datum r).D else (datum r).C)
    (datum r).R (datum r).input.ν (datum r).input.W (datum r).input.P≠0
  inactive : ∀r,(datum r).inactive∈inactiveSubsets (datum r).C (datum r).D

/-- Invoke the original native nonzero-block witness producer; no
existence of a favorable allocation is an input. -/
def actualCanonicalSelectedFamily :
    CanonicalSelectedFamily reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex :=by
  let h:=actual_main_low_family_choices reflected s R seed Z Mrow amp xi reserve b firstHeight
    budget hZ key hz1 hz2
    (fun r : Rows=>mainLowSelectedOriginal reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex r) second
  let alloc:=Classical.choose h
  let hrow:=Classical.choose_spec h
  let row:=Classical.choose hrow
  let hgood:=Classical.choose_spec hrow
  exact ⟨alloc,row,fun r=>(hgood r).1,fun r=>(hgood r).2⟩

variable (F : CanonicalSelectedFamily reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex)

def CanonicalSelectedFamily.chain (r : Rows) : Chain s :=
  geometryLowActualChain reflected s R seed Z Mrow amp xi reserve b firstHeight budget hZ key
    (firstIndex r.val.1) hz1 hz2 r.val.2 second (F.allocation r)

variable (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
  (geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0)

def CanonicalSelectedFamily.geometry (r : Rows) :
    LiveMainGeometry s (F.chain reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex r)
      Z Mrow amp (frequencyLoss Z 32 xi+reserve) xi b budget :=
  geometryLowActualGeometry reflected s R seed Z Mrow amp xi reserve b firstHeight budget hZ key
    (firstIndex r.val.1) hz1 hz2 r.val.2 second (F.allocation r) (F.row r) (hf1 r.val.1) (F.frozen r)

/-- The canonical-to-actual source frame is literal for the SAME selected
native witnesses. The final source height remains free in every later
column invocation and is not substituted for the first-column height. -/
def CanonicalSelectedFamily.frame (r : Rows) :
    CanonicalSourceFrame s
      (F.chain reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex r)
      (F.geometry reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex hf1 r)
      (datum r) second :=
  actual_canonical_source_frame reflected s R seed Z Mrow amp xi reserve b firstHeight budget hZ key
    (firstIndex r.val.1) hz1 hz2 r.val.2 second (F.allocation r) (F.row r) (hf1 r.val.1) (F.frozen r)


/-- The actual payment dictionary sees exactly this complete selected
family, independently of the later source ray, residual shell, or child.
In particular its nominal/own-norm/low-allowance inputs and physical first
radius are the literal native labels used by the OLD summation theorem. -/
def CanonicalSelectedFamily.paidFields (r : Rows) :=
  actual_geometry_low_paid_fields reflected s R seed Z Mrow amp xi reserve b firstHeight budget hZ key
    (firstIndex r.val.1) hz1 hz2 r.val.2
    (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
      hZ key hz1 hz2 firstIndex r)
    second (F.allocation r) (F.row r) (hf1 r.val.1) (F.frozen r)

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualCanonicalSelectedFamily
#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.frame

#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.paidFields
