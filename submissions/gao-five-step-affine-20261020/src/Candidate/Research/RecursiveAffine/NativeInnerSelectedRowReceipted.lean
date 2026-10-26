/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalReceiptedEnergy
import Candidate.Research.RecursiveAffine.NativeSelectedPaidPrefixBindings
import Candidate.Research.RecursiveAffine.NativeSelectedFamilyPrefix
import Candidate.Research.RecursiveAffine.NativeAllRowMasks

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
open Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153AnalyticPrimitive Cycle153.RegionalSchedule
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
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalInnerDaughterPackage
open CenteredMomentFirstDiscardedEnergy CenteredMomentOriginalCommonHarmonic
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant

/-- The actual canonical selected row uses its native chosen witnesses and prefix.
No prefix, child geometry, column or daughter energy bound is assumed. -/
def actualInnerSelectedRowReceipted
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (hm : Matches M H hH (N.input hH) C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hSourceMesh : C.slotMesh≤localSlotMesh epsNode)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+N.height+N.localBase^g.τ/2≤5*N.localBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*N.localBase^g.τ)^2≤(N.localBase^(31:ℝ))^(3:ℝ))
    (reflected second : Bool)(Mrow firstHeight : ℝ)(hMrow : Mrow≤2)(hMrowActual : Mrow=N.state.rowWidth)
    (epsV : ℝ)(hepsV0 : 0≤epsV)(hepsV : epsV≤1)
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
    (Ds : Finset (Ideal O))(zs : Finset O)(T : ℝ)
    (hMask :
      let datum:=geometryLowSecondDatum reflected (N.input hH) N.state.puncture 1 N.localBase
        Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
        N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
      let E:=if second then datum.D else datum.C
      datum.R*E≠0 ∧ ((datum.R*E).absNorm:ℝ)≤N.localBase^(28:ℝ) ∧ Supported E ∧ datum.seed∣E)
    (hfit : Mrow+Real.logb N.localBase ((N.input hH).η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2)
    (hconstants : Real.logb N.localBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+Real.logb N.localBase 1+
      Real.logb N.localBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤(nativeMu/8)/2)
    (hslots : letI : Cycle63.AffineLedger:=N.ledger
      Cycle63.AffineLedger.slotFloor≤∑i,Real.logb N.localBase ((N.input hH).P i) ∧
      (∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.slotTop)
    (haff : letI : Cycle63.AffineLedger:=N.ledger
      length N.localBase (N.input hH).X₁+length N.localBase (N.input hH).X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.B)
    (hpad : supportPadding (Fintype.card N.slots) (9/4) (N.input hH).b₁ (N.input hH).b₂ N.localBase≤nativeMu/8)
    (homega : frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8≤(1/1000000000000000:ℝ))
    (hdelta : nativeMu/8+(nativeMu/64)/2≤(1/1000000000000000:ℝ))
    (hT : 1≤T)(hDs : ∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T)
    (chi0 chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<N.localBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+
        Real.logb N.localBase (max 1 (N.input hH).b₁*max 1 (N.input hH).b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (rateBudget : ℕ)(box0 : Finset (Fin 4→ℤ))(massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
      (geometryFirstLabel (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (hgridFine : (1/C.gridDenominator:ℝ)≤1/10000000000000000000000000000000000000000) :=
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
  let frame:=F.frame reflected second s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex hf1 r
  let hP : ch.R₂*ch.E₂≠0:=hMask.1
  let hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤N.localBase^(28:ℝ):=hMask.2.1
  let hOwn : Supported ch.E₂:=hMask.2.2.1
  let hseed : datum.seed∣ch.E₂:=hMask.2.2.2
  let ray:=if second then psi⁻¹ else chi
  let pNext:=actualInnerSelectedPrefix hH N reflected second Mrow firstHeight hMrow epsV hepsV0 hepsV
    caps.sourceCap hprefixSmall key hz1 hz2 firstIndex hf1 r ray hMask
  let bindings:=actualInnerSelectedPaidPrefixBindings hH N reflected second Mrow firstHeight hMrow
    epsV hepsV0 hepsV caps.sourceCap hprefixSmall key hz1 hz2 firstIndex hf1 r ray hMask massLoss sideError hside
  let paid:=actualSelectedPaidNode N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
    key hz1 hz2 firstIndex massLoss sideError hside r
  let energy:=actualInnerCanonicalReceiptedEnergy hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh ch Mrow gg ray hP hPN Ds zs T
    hOwn datum.seed hseed hfit hconstants hslots haff hpad homega hdelta hT hDs datum second frame
    chi0 chi psi m hm0 hml hm2 hTsource hBetaHigh rfl rfl hfinite hgrid reflected firstHeight epsV rateBudget key hz1 hz2 firstIndex r
    massLoss sideError hside ((nodeInputPresentation hH N).unit (!reflected)) box0
  fun hzs (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))(degree : Fin 4→ℕ)=>
  let boxes : Fin 4→ℕ→Finset (Fin 4→ℤ):=fun _ _=>box0
  fun (hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj)) (boxes (nextInner j hj))))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode)
    (hsource : paid.SourceGates)(hfine : paid.FineSourceGates)
    (hfee : ∀(R : Finset N.slots)(hsum : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh),
      (actualNodeGlobalFee (hH:=hH) N epsNode rateBudget R hsum).amount≤1/1000000000000000)=>
  energy hzs pNext.val pNext.property.2.1 constant eps Bsrc control degree hIH hconstant heps hchild
    hMrowActual bindings.1 hsource hfine bindings.2.1 bindings.2.2 hfee hgridFine

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerSelectedRowReceipted
