/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalEnergy
import Candidate.Research.RecursiveAffine.NativeLiteralColumnSource

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
open Cycle153JointCount
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

private theorem input_X1 : (N.input hH).X₁=N.X1:=rfl
private theorem input_X2 : (N.input hH).X₂=N.X2:=rfl
private theorem input_lower : 1≤(N.input hH).lower:=le_rfl
attribute [local irreducible] ReachableNode.input
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalInnerDaughterPackage
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant

/-- Apply the literal canonical source operator and construct all three
recursive callbacks from the SAME physical daughter. The primitive input
conditions are the actual native source fit, finite-error, canonical-row
and prefix gates; no column, daughter or node-energy bound is an input.
The only recursive input is availability of genuine strictly deeper
NodeOutputs, chosen before this source configuration. -/
def InnerCanonicalReceiptedAt
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
    (ch : Chain (N.input hH))(Mrow : ℝ)
    (gg : LiveMainGeometry (N.input hH) ch N.localBase Mrow (nodeSourceAmp N)
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) (nativeMu/64) (9/4) (Fintype.card N.slots))
    (ray : RayFourExpansion.RayCharacter)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤N.localBase^(28:ℝ))
    (Ds : Finset (Ideal O))(zs : Finset O)(T : ℝ)
    (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂)
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
    (datum : SecondInputDatum N.slots)(second : Bool)
    (frame : CanonicalSourceFrame (N.input hH) ch gg datum second)
    (chi0 chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<N.localBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hray : ray=(if second then psi⁻¹ else chi))
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+
        Real.logb N.localBase (max 1 (N.input hH).b₁*max 1 (N.input hH).b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (reflected : Bool)(firstHeight epsRow : ℝ)(rateBudget : ℕ)
    (key : ℤ×(Fin 5→ℤ)){Label : Type}[Fintype Label]
    (hz1 : (N.input hH).W₁ 0=0)(hz2 : (N.input hH).W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1
      (N.localBase^Mrow) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (labelRow : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
      (geometryFirstLabel (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (units : FirstSourceLabel→O)(box0 : Finset (Fin 4→ℤ)) : Prop :=
  letI : Cycle63.AffineLedger:=N.ledger
  let s:=N.input hH
  let omega:=frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8
  let st:=retainedState N.localBase 28 N.localBase_gt_one (gg.datum.τ ray)
    (internalQ C.Q C.etaSeed) (ch.R₂*ch.E₂) hP hPN gg.datum.radius gg.datum.C gg.datum.D gg.datum.inactive
  let u:=nativeUnit 1 N.localBase (nodeSourceAmp N) omega (nativeMu/8) (nativeMu/64)
    ch.C₁ gg.D₁ gg.datum.C gg.datum.D gg.datum.inactive
  let width:=actual_inner_source_unit N s ch Mrow omega (nativeMu/64) (nativeMu/8) (9/4)
    (Fintype.card N.slots) gg (actual_node_canonical_scalar_gates N).2.1 (by norm_num)
    ray (internalQ C.Q C.etaSeed) hP hPN hfit hconstants rfl
  let hpDatum : datum.R*(if second then datum.D else datum.C)≠0:=by
    simpa only [frame.puncture_eq,frame.own_eq] using hP
  let hnDatum : ((datum.R*(if second then datum.D else datum.C)).absNorm:ℝ)≤N.localBase^(28:ℝ):=by
    simpa only [frame.puncture_eq,frame.own_eq] using hPN
  let ordinaryRows:=mainLowSourceRows second (ordinarySecondDatum datum chi0 (internalQ C.Q C.etaSeed) m) (fun _=>True)
  let selector:=mainLowCanonicalSelector M H hH datum chi0 chi psi (internalQ C.Q C.etaSeed) C.fixed_small
    m hm0 hml hm2 N.localBase 28 N.localBase_gt_one second hpDatum hnDatum C.etaSeed
    (inf_le_left.trans C.Q_le_M) inf_le_right g.e (N.localBase^g.τ) g.e_pos hTsource hbeta hBetaHigh
  ∀(hzs : ∀z∈zs,z∈mainLowPaymentRows ordinaryRows selector buffer)
    (P : PrefixHighPresentation (prefixDictionary (nextInner j hj).val C.etaSeed) st.character st.puncture)
    (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ)≤C.globalBase^prefixCap (nextInner j hj).val)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ),
  let boxes : Fin 4→ℕ→Finset (Fin 4→ℤ):=fun _ _=>box0
  ∀(hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj)) (boxes (nextInner j hj))))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode),
  let p:=actualSelectedPaidNode N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) epsRow (9/4) firstHeight (Fintype.card N.slots)
    key hz1 hz2 firstIndex massLoss sideError hside labelRow
  ∀(hMrowActual : Mrow=N.state.rowWidth)
    (hcommon : p.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+Real.logb N.localBase (ch.E₂.absNorm:ℝ)))
    (hsource : p.SourceGates)(hfine : p.FineSourceGates)
    (hroot : P.mult=Cycle63Moment.childMultiplier (!reflected) N.presentation.mult units
      (nativeLowHistoryCode reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
        N.localBase_gt_one key hz1 hz2 firstIndex labelRow).1)
    (hrelative : N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {P.mult}).absNorm:ℝ)-
      Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
      N.unit*(Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2))
    (hfee : ∀(R : Finset N.slots)(hsum : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh),
      (actualNodeGlobalFee (hH:=hH) N epsNode rateBudget R hsum).amount≤1/1000000000000000)
    (hgridFine : (1/C.gridDenominator:ℝ)≤1/10000000000000000000000000000000000000000),
  let firstInput:=withHeight ch.first (gg.datum.τ ray) sourceHeight
  let Daughter:=Cycle153SourceReturn.PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
  let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
  let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
    ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
  let continues:=fun (d : Daughter)(R : Finset N.slots)=>nativeMainContinuation st u (J d) R
    (fun i=>C.originalWeight i/N.unit)
    (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
  let package:=actualCanonicalInnerDaughterPackage N hj s ch (gg.datum.τ ray) sourceHeight
    (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8) C.slotMesh gg
    (by norm_num) (le_refl _) caps.endpoints.1 (input_lower hH N)
    (input_X1 hH N) (input_X2 hH N) hm.scale (by simp only [omega,mul_one]) hR2 hP hfinite hgrid Ds
  let childAt:=fun (d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
    (z : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
      d.2.2.2 d.2.1.1 d.2.2.1.1 z≠0)(R : Finset N.slots)(hR : R⊆J d)
    (hsum : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh)
    (hcover : R=J d ∨ nodeDetectorDeletion N≤∑i∈R,C.originalWeight i/N.unit)
    (hc : continues d R)=>
    nodeOfNativeContinuation C (nextInner j hj) N.localBase N.unit u 28
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1) N.localBase_eq st width.1
      (package d hn z hne R hR hsum hcover hc).property.2
      (((J d\R).map (originalSubsetEmbedding N.slots))) N.profiles
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
      (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
      (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
      P hPnorm rfl sourceHeight N.height N.height_nonneg
      (by intro k;obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property;rw [←hki];exact N.frequency_bound i)
      (package d hn z hne R hR hsum hcover hc).val
      (package d hn z hne R hR hsum hcover hc).property.1
  let SourceK:=nativeColumnSourceConstant (Fintype.card N.slots) Cs Cpay Kterminal
    (constant (nextInner j hj)) Kcol Cdirect C0 C1 Kdirect
  let Control:=N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect)^2*
    (1+|sourceHeight|+N.height)^(max (max degreeTerminal (degree (nextInner j hj))) degreeDirect)*(2*T)^(3*epsShell)
  let slotLoss:=2*g.δ*31*(Fintype.card N.slots:ℝ)
  let OldPaid:=secondNominal 1 N.localBase (nodeSourceAmp N) omega ch.C₁ gg.D₁ gg.datum.C gg.datum.D
    gg.datum.inactive+nodeSourceAmp N+
    (nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+slotLoss+
      Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*(omega+nativeMu/8)+Cycle63.AffineLedger.q*C.slotMesh)+
    lowAllowance N.localBase ch.C₁ gg.D₁ gg.datum.C gg.datum.D ch.E₂
  ∃(R : Finset N.slots)(F : SuffixFamily (hH:=hH) (nextInner j hj).val (4-(nextInner j hj).val)
      C.etaSeed N.localBase C.Bnorm C.Tz P.mult),
    let paid:=fun rr=>actualSelectedPaidNode N reflected second s N.state.puncture 1 Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) epsRow (9/4) firstHeight (Fintype.card N.slots)
      key hz1 hz2 firstIndex massLoss sideError hside rr
    let weight:=fun rr=>N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second
      (paid rr).first (paid rr).C (paid rr).D (paid rr).inactive N.localBase Mrow
      (Real.logb N.localBase (volume s)) (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsRow 0+
      (innerStage j.val).q*(∑i∈R,C.originalWeight i/N.unit)+massLoss+
      actualInnerRemainingFees (hH:=hH) N epsNode rateBudget)
    let missing:=fun rr=>Real.logb N.localBase ((firstSourceMissing (!reflected) (paid rr).first).absNorm:ℝ)
    (F=emptyReturnedForest ∨ Nonempty (ChosenInnerColumn N hj reflected s N.state.puncture 1 Mrow
      (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      key hz1 hz2 firstIndex units weight missing (Bsrc (nextInner j hj)) (fun _=>box0)
      (fun _=>P.mult) (fun _=>F) labelRow)) ∧
    (∑D∈Ds,∑z∈zs,(1:ℝ)*‖CenteredMomentCommonPairedSource.normalizedColumn firstInput ch.E₂ hOwn ch.R₂ seed D z‖^2)≤
      SourceK*Control*(ch.E₂.absNorm:ℝ)^(epsShell-1)*
        (N.localBase^OldPaid+N.localBase^(slotLoss+Cycle63.AffineLedger.q*((∑i∈R,C.originalWeight i/N.unit)+C.slotMesh))*F.value)*
        N.localBase^(actualNodeLocalSourcePad (hH:=hH) N)

end
end OAI.SevenEighths.Cycle153ActualColumn
