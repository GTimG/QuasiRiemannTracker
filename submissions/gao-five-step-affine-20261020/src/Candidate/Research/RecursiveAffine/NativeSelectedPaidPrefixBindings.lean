/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerSelectedPrefix
import Candidate.Research.RecursiveAffine.NativeSelectedRawFields
import Candidate.Research.RecursiveAffine.NativeLowHistoryCode
import Candidate.Research.RecursiveAffine.NativeNodeSourceGates

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open LocalMoment ConcretePrimeRowBridge CenteredMomentSecondHeightFamily Cycle153CanonicalLow
open Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153.RegionalSchedule Cycle153JointCount
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

open CenteredMomentFirstDiscardedEnergy CenteredMomentOriginalCommonHarmonic Cycle153JointCount
attribute [local irreducible] ReachableNode.input

/-- SAME actual selected family and native prefix, independently of every energy/continuation output. -/
def actualInnerSelectedPaidPrefixBindings
    (reflected second : Bool)(Mrow firstHeight : ℝ)(hMrow : Mrow≤2)
    (epsV : ℝ)(hepsV0 : 0≤epsV)(hepsV : epsV≤1)
    (hsource : sourceRadius (N.input hH)≤N.localBase^(3:ℝ))
    (hprefixSmall : Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2≤1)
    (key : ℤ×(Fin 5→ℤ)){Label : Type}[Fintype Label]
    (hz1 : (N.input hH).W₁ 0=0)(hz2 : (N.input hH).W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1
      (N.localBase^Mrow) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val)
      N.state.puncture (N.input hH).ν (N.input hH).W (N.input hH).P≠0)
    (r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex)
    (ray : RayFourExpansion.RayCharacter)
    (hMask :
      let datum:=geometryLowSecondDatum reflected (N.input hH) N.state.puncture 1 N.localBase
        Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
        N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
      let E:=if second then datum.D else datum.C
      datum.R*E≠0 ∧ ((datum.R*E).absNorm:ℝ)≤N.localBase^(28:ℝ) ∧ Supported E ∧ datum.seed∣E)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
      (geometryFirstLabel (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
 :=
  letI : Cycle63.AffineLedger:=N.ledger
  let s:=N.input hH
  let F:=actualCanonicalSelectedFamily reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex
  let ch:=F.chain reflected second s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex r
  let gg:=F.geometry reflected second s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex hf1 r
  let datum:=geometryLowSecondDatum reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
  let hP : ch.R₂*ch.E₂≠0:=hMask.1
  let hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤N.localBase^(28:ℝ):=hMask.2.1
  let hOwn : Supported ch.E₂:=hMask.2.2.1
  let hseed : datum.seed∣ch.E₂:=hMask.2.2.2
  let P0:=nodeInputPresentation hH N
  let pNext:=actualInnerSelectedPrefix hH N reflected second Mrow firstHeight hMrow epsV hepsV0 hepsV
    hsource hprefixSmall key hz1 hz2 firstIndex hf1 r ray hMask
  let p:=actualSelectedPaidNode N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
    key hz1 hz2 firstIndex massLoss sideError hside r
  let first:=geometryFirstLabel s N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex r.val.1).1.val
  let code:=nativeLowHistoryCode reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex r
  show p.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+Real.logb N.localBase (ch.E₂.absNorm:ℝ)) ∧
    pNext.val.mult=Cycle63Moment.childMultiplier (!reflected) N.presentation.mult (P0.unit (!reflected)) code.1 ∧
    N.unit*(retainedState N.localBase 28 N.localBase_gt_one (gg.datum.τ ray) (internalQ C.Q C.etaSeed)
      (ch.R₂*ch.E₂) hP hPN gg.datum.radius gg.datum.C gg.datum.D gg.datum.inactive).rowWidth+
      Real.logb C.globalBase ((Ideal.span {pNext.val.mult}).absNorm:ℝ)-
      Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
      N.unit*(Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2) from by
    refine ⟨?_,?_,?_⟩
    · exact actual_selected_paid_node_chain_fields N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r (F.allocation r)
    · have hp:=pNext.property.1
      exact hp.trans (congrArg (fun root=>Cycle63Moment.childMultiplier (!reflected) root (P0.unit (!reflected)) code.1)
        (nodeInputPresentation_mult hH N))
    · have hp:=pNext.property.2.2
      have hlog:=congrArg (fun root=>Real.logb C.globalBase ((Ideal.span {root}).absNorm:ℝ))
        (nodeInputPresentation_mult hH N)
      have hcoord:=actual_selected_paid_node_coordinates N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r 2
      have hcoord' : p.coordinate 2=N.unit*actualHighCoordinates reflected (!reflected) second first
          datum.C datum.D datum.inactive N.localBase Mrow (Real.logb N.localBase (volume s))
          (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 2 :=by
        exact hcoord
      change N.unit*(retainedState N.localBase 28 N.localBase_gt_one (gg.datum.τ ray) (internalQ C.Q C.etaSeed)
        (ch.R₂*ch.E₂) hP hPN gg.datum.radius gg.datum.C gg.datum.D gg.datum.inactive).rowWidth+
        Real.logb C.globalBase ((Ideal.span {pNext.val.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ) ≤
        N.unit*actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
        N.localBase Mrow (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 2+
        N.unit*(Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2) at hp
      linarith only [hp,hlog,hcoord']


end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerSelectedPaidPrefixBindings
