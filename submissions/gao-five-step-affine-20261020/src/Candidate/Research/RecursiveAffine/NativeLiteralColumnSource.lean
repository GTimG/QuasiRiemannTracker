/- Named SAME physical Common continuation node for native Column traces.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalInnerCoordinatePacket
import Candidate.Research.RecursiveAffine.NativeInnerColumnLiteralFields
import Candidate.Research.RecursiveAffine.NativeInnerColumnLiteralCoordinates
import Candidate.Research.RecursiveAffine.NativeLiteralChosenColumn
import Candidate.Research.RecursiveAffine.NativeLiteralPhysicalEdge
import Candidate.Research.RecursiveAffine.NativeActualSourceChild

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option maxHeartbeats 200000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentEnergyState Cycle153HighProvider Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity CenteredMomentDivisorAllocation
open Cycle153SourceReturn Cycle63FinalCapacity
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonRawScale
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentAllocatedRayDictionary
open Cycle63FinalLow Cycle63InitialMass Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit
open Cycle153Geometry Cycle153JointCount Cycle153ReachableGeometry
open RayFourExpansion
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M   ≤   H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
attribute [local irreducible] ReachableNode.input actualSelectedPaidNode
attribute [local irreducible] actualCanonicalInnerDaughterPackage actual_inner_column_literal_fields
attribute [local irreducible] actual_literal_inner_physical_edge

/-- The literal node used by native Column traces is constructed from
ONE genuine same-daughter geometry/history/mask package. The retained
prefix, profile, independent source height and original frequency height
are unchanged. There is no node energy or output selection here. -/
def actual_literal_inner_column_source
    (N : ReachableNode C j)(hj : j.val<3)
    (s : Input N.slots)(ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (n : ℕ)(b Mrow omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1   ≤   b)(hcard : Fintype.card N.slots   ≤   n)(hs : s.upper   ≤   b)(hlower : 1   ≤   s.lower)
    (hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)   ≤   N.localBase^(28:ℝ))
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂))   ≤   1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)   ≤   positionMargin)
    (Ds : Finset (Ideal O))(sourceRay : RayFourExpansion.RayCharacter)
    (hcharacter : sourceCharacter=g.datum.τ sourceRay) :=
    let st:=retainedState N.localBase 28 N.localBase_gt_one (g.datum.τ sourceRay)
      (internalQ C.Q C.etaSeed) (ch.R₂*ch.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first sourceCharacter sourceHeight
    let u:=nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    fun(hwidth : st.width   ≤   u)
      (P : PrefixHighPresentation (prefixDictionary (nextInner j hj).val C.etaSeed) st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ)   ≤   C.globalBase^prefixCap (nextInner j hj).val)=>
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
    let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    fun(d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
      (row : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
        d.2.2.2 d.2.1.1 d.2.2.1.1 row≠0)
      (R : Finset N.slots)(hR : R⊆J d)
      (hsum : (∑i∈R,C.originalWeight i/N.unit)   ≤   nodeDetectorDeletion N+C.slotMesh)
      (hcover : R=J d ∨ nodeDetectorDeletion N   ≤   ∑i∈R,C.originalWeight i/N.unit)
      (hc : nativeMainContinuation N.state u (J d) R (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1))=>
    fun (reflected second : Bool)(Rsource seed : Ideal O)(epsRow firstHeight : ℝ)
      (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
      (firstIndex : Label→GeometryLowFirstIndex reflected s Rsource seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
      (r : NativeLowRows reflected s Rsource seed N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)
      (massLoss sideError : ℝ)
      (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
        (geometryFirstLabel s Rsource seed (N.localBase^Mrow) N.localBase xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
      (hinput : s=N.input hH)(hMrowActual : Mrow=N.state.rowWidth)
      (epsNode : ℝ)(feeBudget : ℕ)
      (deleted : (NativeLowRows reflected s Rsource seed N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)→Finset N.slots)(hdeleted : deleted r=R)=>
    let p:=actualSelectedPaidNode N reflected second s Rsource seed Mrow (nodeSourceAmp N) xi reserve epsRow b
      firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r
    let fee:=actualNodeGlobalFee (hH:=hH) N epsNode feeBudget R hsum
    fun (hcommon : p.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+Real.logb N.localBase (ch.E₂.absNorm:ℝ)))
      (source : p.SourceGates)(fine : p.FineSourceGates)
      (hfee : fee.amount ≤ 1/1000000000000000)(hxi : xi ≤ 1/1000000000000000)
      (hgridFine : (1/C.gridDenominator:ℝ) ≤ 1/10000000000000000000000000000000000000000)
      (units : FirstSourceLabel→O)
      (hroot : P.mult=Cycle63Moment.childMultiplier (!reflected) N.presentation.mult units
        (nativeLowHistoryCode reflected s Rsource seed N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight n
          N.localBase_gt_one key hz1 hz2 firstIndex r).1)
      (hrelative : N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {P.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
        N.unit*(Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2))=>
    let packet:=actualCanonicalInnerDaughterPackage N hj s ch sourceCharacter sourceHeight n b Mrow omega xi reserve C.slotMesh
      g hb hcard hs hlower hX1 hX2 hscale homega hR2 hP hfinite hgrid Ds
      d hn row hne R hR hsum hcover hc
    let chosen:=nodeOfNativeContinuation C (nextInner j hj) N.localBase N.unit u 28
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1) N.localBase_eq st hwidth packet.property.2
      (((J d\R).map (originalSubsetEmbedding N.slots))) N.profiles
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
      (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
      (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
      P hPnorm rfl sourceHeight N.height N.height_nonneg
      (by intro k;obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property;rw [←hki];exact N.frequency_bound i)
      packet.val packet.property.1
    fun (constant childEps Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
      (boxes : ℕ→Finset (Fin 4→ℤ))
      (out : NodeOutput hH chosen constant childEps Bsrc control degree (fun k=>boxes (k+1)))
      (rawRoot : (NativeLowRows reflected s Rsource seed N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)→O)
      (rawFamily : (rr : NativeLowRows reflected s Rsource seed N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
        C.etaSeed N.localBase C.Bnorm C.Tz (rawRoot rr))
      (hvalue : (rawFamily r).value=out.family.value)=>
    let paidFields:=actual_selected_paid_node_fields N reflected second s Rsource seed Mrow (nodeSourceAmp N)
      xi reserve epsRow b firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r
    let hunit : p.unit=N.unit:=paidFields.1
    let hrow : p.scale=N.unit*N.state.rowWidth:=
      paidFields.2.1.trans (congrArg (fun x=>N.unit*x) hMrowActual)
    let hvolume : p.volumeLength=N.unit*Real.logb N.localBase (volume (N.input hH)):=
      paidFields.2.2.1.trans (congrArg (fun ss=>N.unit*Real.logb N.localBase (volume ss)) hinput)
    let hamp : p.amplification=N.unit*nodeSourceAmp N:=paidFields.2.2.2.1
    let fields:=actual_inner_column_literal_fields N hj s ch sourceCharacter sourceHeight n b Mrow omega xi reserve C.slotMesh
      g hb hcard hs hlower hX1 hX2 hscale homega hR2 hP hPN hfinite hgrid Ds sourceRay hcharacter
      hwidth P hPnorm d hn row hne R hR hsum hcover hc
    let sourceEdge:=actual_literal_inner_physical_edge N hj s ch sourceCharacter sourceHeight n b Mrow omega xi reserve C.slotMesh
      g hb hcard hs hlower hX1 hX2 hscale homega hR2 hP hPN hfinite hgrid Ds sourceRay hcharacter
      hwidth P hPnorm d hn row hne R hR hsum hcover hc p hunit hrow hvolume hamp hcommon source fine fee hfee
      rfl (actual_node_fee_model (hH:=hH) N epsNode feeBudget R hsum) hxi hgridFine hrelative
    let paidForWeight:=fun rr=>actualSelectedPaidNode N reflected second s Rsource seed Mrow (nodeSourceAmp N)
      xi reserve epsRow b firstHeight n key hz1 hz2 firstIndex massLoss sideError hside rr
    let weight:=fun rr=>N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second
      (paidForWeight rr).first (paidForWeight rr).C (paidForWeight rr).D (paidForWeight rr).inactive
      N.localBase Mrow (Real.logb N.localBase (volume s)) (nodeSourceAmp N) xi reserve epsRow 0+
      (innerStage j.val).q*(∑i∈deleted rr,C.originalWeight i/N.unit)+massLoss+
      actualInnerRemainingFees (hH:=hH) N epsNode feeBudget)
    let missing:=fun rr=>Real.logb N.localBase ((firstSourceMissing (!reflected) (paidForWeight rr).first).absNorm:ℝ)
    show Nonempty (ChosenInnerColumn N hj reflected s Rsource seed Mrow (nodeSourceAmp N) xi reserve b
      firstHeight n key hz1 hz2 firstIndex units weight missing Bsrc boxes rawRoot rawFamily r) from
    by
      obtain ⟨hu,edge,hnode,hfeeEq⟩:=sourceEdge
      have raw:=actual_chosen_column_scheduled_arithmetic N reflected second s Rsource seed Mrow (nodeSourceAmp N)
        xi reserve epsRow b firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r epsNode
        feeBudget R hsum chosen edge hnode hfeeEq
      refine ⟨{
        child := chosen
        unit := hu
        root := fields.2.2.1.trans hroot
        constant := constant
        epsilon := childEps
        control := control
        degree := degree
        output := out
        edge := edge
        rawWeight := ?_
        rawMissing := raw.2
        value := hvalue }⟩
      change N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second p.first p.C p.D p.inactive
        N.localBase Mrow (Real.logb N.localBase (volume s)) (nodeSourceAmp N) xi reserve epsRow 0+
        (innerStage j.val).q*(∑i∈deleted r,C.originalWeight i/N.unit)+massLoss+
        actualInnerRemainingFees (hH:=hH) N epsNode feeBudget)=_
      rw [hdeleted]
      exact raw.1


end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_literal_inner_column_source

