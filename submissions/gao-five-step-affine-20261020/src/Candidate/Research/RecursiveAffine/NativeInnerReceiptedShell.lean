/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerReceiptedRowsResidual
import Candidate.Research.RecursiveAffine.NativeColumnReceiptShell
import Candidate.Research.RecursiveAffine.NativeChosenColumnReindex
import Candidate.Research.RecursiveAffine.NativeScheduledRawWeight
import Candidate.Research.RecursiveAffine.NativeTerminalNode
import Candidate.Research.RecursiveAffine.NativeRootResidualNormalization
import Candidate.Research.RecursiveAffine.NativeSelectedFamilyResidual
import Candidate.Research.RecursiveAffine.LowPhysical.ActualOldSelectedRows

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
open Cycle153LowPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonicalScalar
open Cycle153ActualSourceGates CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

open Cycle153SourceReturn Cycle153JointCount

private theorem native_paid_weight_transport {Z M X X' q q' d fee fee' : ℝ}
    (hx : X=X')(hq : q=q')(hf : fee=fee') :
    Z^(M+X+q*d+fee)=Z^(M+X'+q'*d+fee'):=by
  cases hx
  cases hq
  cases hf
  rfl

private theorem zero_own_weighted_value {Row : Type*}[Fintype Row]
    {v own : ℝ}{w w' a : Row→ℝ}
    (hv : v=own+∑r,w r*a r)(ho : own=0)(hw : ∀r,w r=w' r) : v=∑r,w' r*a r:=by
  rw [hv,ho,zero_add]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hw r]

private theorem replace_actual_return_value {source outer old A returned value : ℝ}
    (h : source≤outer*old+A*returned)(hv : value=returned) : source≤outer*old+A*value :=by
  simpa only [hv] using h

/-- One actual residual shell produces a licensed LOW-only whole
receipt and its literal source bound. The empty own component adds no
HIGH energy; all continuing children are the SAME genuine chosen outputs. -/
def actualInnerReceiptedShell
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
    (Ds : Finset (Ideal O))(T : ℝ)
    (hMask : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex,
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
    (chi0 : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex→RayFourExpansion.RayCharacter)
    (chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
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
    (hgridFine : (1/C.gridDenominator:ℝ)≤1/10000000000000000000000000000000000000000)
    (hsourcePaid : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex, (actualSelectedPaidNode N reflected second (N.input hH) N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r).SourceGates)
    (hfinePaid : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex, (actualSelectedPaidNode N reflected second (N.input hH) N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r).FineSourceGates)
    (hfee : ∀(R : Finset N.slots)(hsum : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh),
      (actualNodeGlobalFee (hH:=hH) N epsNode rateBudget R hsum).amount≤1/1000000000000000)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ)
    (hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj)) (fun _=>box0)))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode)
    (budget : ℕ)(hcard : Fintype.card N.slots≤budget)(hepsVpos : 0<epsV)
    (hlarge : actualSelectedScalarThreshold budget epsV hepsVpos≤N.localBase)
    (Psi : 𝓢(ℝ,ℂ))(sideLower : ℝ)
    (hmassLoss : massLoss=3*g.δ-sideLower)
    (hmassSide : ∀l,sideLower≤geometryHighSide reflected (Real.logb N.localBase (volume (N.input hH)))
      (geometryExponents (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (firstIndex l).1.val.1.val))
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect)
    (hRate : g.δ=nativeDriverRate rateBudget)
    (hVRate : epsV=postDictionaryRate C.Bnorm rateBudget)
    (hShellRate : epsShell=postDictionaryRate C.Bnorm rateBudget)
    (hBsrc : 0≤Bsrc (nextInner j hj))
    (hinj : Function.Injective (fun l=>(geometryFirstLabel (N.input hH) N.state.puncture 1
      (N.localBase^Mrow) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow
      (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex,
      DecoratedFacts (fun _ : Unit=>N.presentation.mult) (!reflected)
        (fun _=>(nodeInputPresentation hH N).unit (!reflected)) N.localBase (Bsrc (nextInner j hj)) box0
        ((),nativeLowHistoryCode reflected (N.input hH) N.state.puncture 1 N.localBase Mrow
          (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
          N.localBase_gt_one key hz1 hz2 firstIndex r))
    (shift : ℝ)(hshift : shift≤1/1000000000000) :=
  letI : Cycle63.AffineLedger:=N.ledger
  let s:=N.input hH
  let Rows:=NativeLowRows reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex
  let selected:=actualCanonicalSelectedFamily reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex
  let ch:=fun r : Rows=>selected.chain reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex r
  let gg:=fun r : Rows=>selected.geometry reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex hf1 r
  let datum:=fun r : Rows=>geometryLowSecondDatum reflected s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
  let ordinaryRows:=fun r : Rows=>mainLowSourceRows second
    (ordinarySecondDatum (datum r) (chi0 r) (internalQ C.Q C.etaSeed) m) (fun _=>True)
  let selector:=fun r : Rows=>mainLowCanonicalSelector M H hH (datum r) (chi0 r) chi psi
    (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2 N.localBase 28 N.localBase_gt_one
    second (hMask r).1 (hMask r).2.1 C.etaSeed (inf_le_left.trans C.Q_le_M) inf_le_right
    g.e (N.localBase^g.τ) g.e_pos hTsource hbeta hBetaHigh
  let zs:=fun r : Rows=>mainLowPaymentRows (ordinaryRows r) (selector r) buffer
  let first:=fun l=>geometryFirstLabel s N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val
  let label:=fun r : Rows=>actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
    (actual_main_low_selected_inactive reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex r)
  let nominal:=fun r : Rows=>secondNominal 1 N.localBase (nodeSourceAmp N)
    (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8)
    (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
    (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
    (label r).1.1 (label r).1.2 (label r).2.val
  let allowance:=fun r : Rows=>lowAllowance N.localBase
    (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
    (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
    (label r).1.1 (label r).1.2 (if second then (label r).1.2 else (label r).1.1)
  let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
    2*g.δ*31*(Fintype.card N.slots:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8+nativeMu/8)+Cycle63.AffineLedger.q*C.slotMesh
  let mass:=fun l=>geometryFirstHighMass reflected s N.state.puncture 1 Psi Mrow N.localBase (nativeMu/64) g.δ
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val
  let columnEnergy:=fun r : Rows=>∑D∈Ds,∑z∈zs r,(1:ℝ)*‖CenteredMomentCommonPairedSource.normalizedColumn
    (withHeight (ch r).first ((gg r).datum.τ (if second then psi⁻¹ else chi)) sourceHeight)
    (ch r).E₂ (hMask r).2.2.1 (ch r).R₂ (datum r).seed D z‖^2
  let Cg:=nativeColumnSourceConstant (Fintype.card N.slots) Cs Cpay Kterminal
    (constant (nextInner j hj)) Kcol Cdirect C0 C1 Kdirect
  let fixed:=N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect)^2*
    (1+|sourceHeight|+N.height)^(max (max degreeTerminal (degree (nextInner j hj))) degreeDirect)*(2*T)^(3*epsShell)
  let physical:=geometryHighFactor reflected (geometrySupportConstant budget 1 (1/4) (1/4)) key
  let hSource:=actualInnerReceiptedRowsResidual hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh reflected second Mrow firstHeight
    hMrow hMrowActual epsV hepsV0 hepsV hprefixSmall key hz1 hz2 firstIndex hf1 Ds T hMask
    hfit hconstants hslots haff hpad homega hdelta hT hDs chi0 chi psi m hm0 hml hm2
    hTsource hBetaHigh hfinite hgrid rateBudget box0 massLoss sideError hside hgridFine
    hsourcePaid hfinePaid hfee constant eps Bsrc control degree hIH hconstant heps hchild
    budget hcard hepsVpos hlarge Psi sideLower hmassLoss hmassSide
    hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect
  let units:=(nodeInputPresentation hH N).unit (!reflected)
  let rowKey:=nativeLowHistoryCode reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one key hz1 hz2 firstIndex
  let pNext:=fun r : Rows=>actualInnerSelectedPrefix hH N reflected second Mrow firstHeight hMrow
    epsV hepsV0 hepsV caps.sourceCap hprefixSmall key hz1 hz2 firstIndex hf1 r
    (if second then psi⁻¹ else chi) (hMask r)
  let rawRoot:=fun r : Rows=>(pNext r).val.mult
  strengthen_actual_source hSource (fun deleted rawFamily hdata=>by
    let scheduledWeight:=fun r : Rows=>N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second
      (first r.val.1) (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 N.localBase Mrow
      (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 0+
      (innerStage j.val).q*(∑i∈deleted r,C.originalWeight i/N.unit)+
      (massLoss+actualInnerRemainingFees (hH:=hH) N epsNode rateBudget))
    let missing:=fun r : Rows=>Real.logb N.localBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)
    have chosen : ∀r,rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenInnerColumn N hj reflected s
        N.state.puncture 1 Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight
        (Fintype.card N.slots) key hz1 hz2 firstIndex units scheduledWeight missing
        (Bsrc (nextInner j hj)) (fun _=>box0) rawRoot rawFamily r):=by
      intro r
      rcases (hdata.1.1 r).1 with hz|⟨oldChoice⟩
      · exact Or.inl hz
      · obtain ⟨picked⟩:=oldChoice
        refine Or.inr ⟨ChosenInnerColumn.reindexAnalytic N hj reflected s N.state.puncture 1
          Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight
          (Fintype.card N.slots) key hz1 hz2 firstIndex units _ _ (Bsrc (nextInner j hj))
          (fun _=>box0) _ _ r picked scheduledWeight missing rawRoot rawFamily ?_ ?_ ?_⟩
        all_goals try rfl
        let c:=Mrow+actualHighCoordinates reflected (!reflected) second
          (first r.val.1) (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 N.localBase Mrow
          (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 0+
          (innerStage j.val).q*(∑i∈deleted r,C.originalWeight i/N.unit)
        change N.localBase^(c+(massLoss+actualInnerRemainingFees (hH:=hH) N epsNode rateBudget))=
          N.localBase^(c+massLoss+actualInnerRemainingFees (hH:=hH) N epsNode rateBudget)
        congr 1
        ring
    let own:=ReturnedPartAt.empty (M:=M) (H:=H) (hH:=hH) (innerStage j.val).q (prefixDictionary (j.val+1)) C.etaSeed
      N.localBase C.Bnorm C.Tz N.presentation.mult N.state.rowWidth
      (Real.logb N.localBase (volume (N.input hH))) (nodeSourceAmp N) 0
    have ownValue : own.value=0:=by
      simp only [own,ReturnedPartAt.value,ReturnedPartAt.empty,SecondStepHighCount.empty_value,Finset.sum_const_zero]
    have ownClass : ∀b,(Fintype.card (own.record b).Class:ℝ)≤C.highClassCap:=by
      intro b
      have hz : Fintype.card (own.record b).Class=0:=
        Fintype.card_eq_zero_iff.mpr ⟨fun x=>Empty.elim x⟩
      have hzR : (Fintype.card (own.record b).Class:ℝ)=0:=by exact_mod_cast hz
      exact hzR.le.trans C.highClassCap_nonneg
    have ownAmp : own.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))):=
      (nodeSourceAmp_eq_native N).symm
    have error0 : 0≤42/(C.gridDenominator:ℝ):=by positivity
    have errorFine : 42/(C.gridDenominator:ℝ)≤1/1000000000000:=by
      have hh:=mul_le_mul_of_nonneg_left hgridFine (by norm_num : (0:ℝ)≤42)
      simpa only [mul_one_div] using hh.trans (by norm_num)
    have ampBound : N.unit*own.amp≤
        ![Cycle153Geometry.Coordinates.a1 N.coordinates,Cycle153Geometry.Coordinates.a2 N.coordinates,
          Cycle153Geometry.Coordinates.a3 N.coordinates,Cycle153Geometry.Coordinates.a4 N.coordinates] j+
          42/C.gridDenominator:=by
      rw [ownAmp]
      exact node_own_amplifier_receipt N
    have ownRoom : own.loss+shift≤terminalLossCap j:=by
      change 0+shift≤terminalLossCap j
      have hj3 : (j.val:ℝ)≤3:=by exact_mod_cast (show j.val≤3 from Nat.le_of_lt_succ j.isLt)
      dsimp only [terminalLossCap]
      linarith only [hshift,hj3]
    obtain ⟨receipt,hvalue,hloss⟩:=actual_inner_shell_receipt_from_chosen_columns N hj reflected second s
      N.state.puncture 1 Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight
      (Fintype.card N.slots) key hz1 hz2 firstIndex units own
      (fun i=>C.originalWeight i/N.unit) deleted (innerStage j.val).q
      (fun _=>massLoss+actualInnerRemainingFees (hH:=hH) N epsNode rateBudget) rawRoot rawFamily
      (Bsrc (nextInner j hj)) (fun _=>box0) hBsrc hinj sourceFacts rfl rfl ownAmp
      (42/C.gridDenominator) error0 errorFine ampBound (terminalLossCap_nonneg j) ownClass
      chosen shift hshift ownRoom
    let analyticWeight:=fun r : Rows=>N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second
      (first r.val.1) (label r).1.1 (label r).1.2 (label r).2.val N.localBase Mrow
      (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 0+
      Cycle63.AffineLedger.q*(∑i∈deleted r,C.originalWeight i/N.unit)+
      (massLoss+3*g.δ+oldLoss epsNode+epsV+130*epsShell+actualNodeLocalSourcePad (hH:=hH) N+
        2*g.δ*31*(Fintype.card N.slots:ℝ)+Cycle63.AffineLedger.q*C.slotMesh))
    have weightEq : ∀r,scheduledWeight r=analyticWeight r:=by
      intro r
      have hcoord : actualHighCoordinates reflected (!reflected) second
          (first r.val.1) (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 N.localBase Mrow
          (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 0=
        actualHighCoordinates reflected (!reflected) second
          (first r.val.1) (label r).1.1 (label r).1.2 (label r).2.val N.localBase Mrow
          (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV 0:=rfl
      have hq : (innerStage j.val).q=Cycle63.AffineLedger.q:=rfl
      have hfees : massLoss+actualInnerRemainingFees (hH:=hH) N epsNode rateBudget=
          massLoss+3*g.δ+oldLoss epsNode+epsV+130*epsShell+actualNodeLocalSourcePad (hH:=hH) N+
          2*g.δ*31*(Fintype.card N.slots:ℝ)+Cycle63.AffineLedger.q*C.slotMesh:=by
        dsimp only [actualInnerRemainingFees]
        rw [hRate,hVRate,hShellRate]
        change massLoss+(3*nativeDriverRate rateBudget+oldLoss epsNode+postDictionaryRate C.Bnorm rateBudget+
          130*postDictionaryRate C.Bnorm rateBudget+actualNodeLocalSourcePad (hH:=hH) N+
          2*nativeDriverRate rateBudget*31*(Fintype.card N.slots:ℝ)+(innerStage j.val).q*C.slotMesh)=_
        change _=massLoss+3*nativeDriverRate rateBudget+oldLoss epsNode+postDictionaryRate C.Bnorm rateBudget+
          130*postDictionaryRate C.Bnorm rateBudget+actualNodeLocalSourcePad (hH:=hH) N+
          2*nativeDriverRate rateBudget*31*(Fintype.card N.slots:ℝ)+(innerStage j.val).q*C.slotMesh
        ring
      exact native_paid_weight_transport hcoord hq hfees
    have receiptValue : receipt.family.value=∑r : Rows,analyticWeight r*(rawFamily r).value:=
      zero_own_weighted_value hvalue ownValue weightEq
    let hraw:=replace_actual_return_value hdata.2 receiptValue
    let fixedBase:=N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect)^2*
      (1+|sourceHeight|+N.height)^(max (max degreeTerminal (degree (nextInner j hj))) degreeDirect)
    let factor:=(2*T)^(3*epsShell)
    let oldFactor:=native_old_selected_cost_mul_factor reflected second s N.state.puncture
      N.localBase Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight
      (Fintype.card N.slots) N.localBase_gt_one key hz1 hz2 firstIndex Psi g.δ epsShell
      (common+actualNodeLocalSourcePad (hH:=hH) N) Cg fixedBase factor
    let normalized:=actual_root_residual_shell_normalization
      (zero_lt_one.trans N.localBase_gt_one) hraw oldFactor rfl
    exact Exists.intro receipt (And.intro hloss normalized))

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerReceiptedShell
