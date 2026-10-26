/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedFamilyPrefix
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
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153.RegionalSchedule
private def presentationAtCharacter {Base : Type}{base : Base→Character}
    {eta eta' : Character}{R : Ideal O}(h : eta=eta')
    (P : PrefixHighPresentation base eta R) : PrefixHighPresentation base eta' R:=h▸P
private theorem presentationAtCharacter_mult {Base : Type}{base : Base→Character}
    {eta eta' : Character}{R : Ideal O}(h : eta=eta')
    (P : PrefixHighPresentation base eta R) : (presentationAtCharacter h P).mult=P.mult:=by
  cases h
  rfl
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

private theorem input_eta : (N.input hH).η=N.state.character:=rfl
private theorem input_X1 : (N.input hH).X₁=N.X1:=rfl
private theorem input_X2 : (N.input hH).X₂=N.X2:=rfl
private theorem input_lower : 1≤(N.input hH).lower:=le_rfl
attribute [local irreducible] ReachableNode.input
open CenteredMomentFirstDiscardedEnergy CenteredMomentOriginalCommonHarmonic

/-- The parent's genuine source dictionary viewed at its literal affine input character. -/
def nodeInputPresentation : PrefixHighPresentation (prefixDictionary j.val C.etaSeed)
    (N.input hH).η N.state.puncture:=presentationAtCharacter (input_eta hH N).symm N.presentation
@[simp] theorem nodeInputPresentation_mult : (nodeInputPresentation hH N).mult=N.presentation.mult:=
  presentationAtCharacter_mult (input_eta hH N).symm N.presentation

/-- SAME actual selected family and native prefix, independently of every energy/continuation output. -/
def actualInnerSelectedPrefix
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
  let hP0 : P0.mult=N.presentation.mult:=nodeInputPresentation_mult hH N
  let pNext:=F.actualPrefix N reflected second s N.state.puncture P0 hP0 Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight epsV (Fintype.card N.slots) hMrow
    (actual_node_canonical_scalar_gates N).2.1
    (add_nonneg (frequencyLoss_nonneg N.localBase 32 (nativeMu/64) N.localBase_gt_one (by norm_num)
      (div_nonneg nativeMu_pos.le (by norm_num))) (div_nonneg nativeMu_pos.le (by norm_num)))
    hepsV0 hepsV (by norm_num) hprefixSmall hsource key hz1 hz2 firstIndex hf1 r ray hP hPN
  pNext

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerSelectedPrefix
