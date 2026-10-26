/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalReceiptedResult
import Candidate.Research.RecursiveAffine.NativePhysicalEdgeForFields

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
open Cycle153JointCount Cycle153Geometry
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
private theorem receipted_direct_rate_le_half (k : Fin 4) : directNodeRate k≤1/2:=by
  fin_cases k <;> norm_num [directNodeRate,innerStage,Cycle153.FixedStages.stage1,
    Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,
    Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound,
    Cycle153Geometry.Coordinates.q1,Cycle153Geometry.Coordinates.q2,
    Cycle153Geometry.Coordinates.q3,Cycle153Geometry.Coordinates.q4]

variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

private theorem input_X1 : (N.input hH).X₁=N.X1:=rfl
private theorem input_X2 : (N.input hH).X₂=N.X2:=rfl
private theorem input_lower : 1≤(N.input hH).lower:=le_rfl
attribute [local irreducible] ReachableNode.input
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalInnerDaughterPackage actualCanonicalInnerCoordinatePacket
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant
attribute [local irreducible] actual_literal_inner_column_source actualInnerCanonicalEnergy actualSelectedPaidNode

/-- Apply the literal canonical source operator and construct all three
recursive callbacks from the SAME physical daughter. The primitive input
conditions are the actual native source fit, finite-error, canonical-row
and prefix gates; no column, daughter or node-energy bound is an input.
The only recursive input is availability of genuine strictly deeper
NodeOutputs, chosen before this source configuration. -/
def actualInnerCanonicalReceiptedEnergy
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
    (units : FirstSourceLabel→O)(box0 : Finset (Fin 4→ℤ)) :
    InnerCanonicalReceiptedAt hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
      source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh ch Mrow gg ray hP hPN Ds zs T
      hOwn seed hseed hfit hconstants hslots haff hpad homega hdelta hT hDs datum second frame
      chi0 chi psi m hm0 hml hm2 hTsource hBetaHigh hray hR2 hfinite hgrid
      reflected firstHeight epsRow rateBudget key hz1 hz2 firstIndex labelRow massLoss sideError hside units box0 :=by
  unfold InnerCanonicalReceiptedAt
  intro s omega st u width hpDatum hnDatum ordinaryRows selector
    hzs P hPnorm constant eps Bsrc control degree boxes hIH hconstant heps hchild
    p hMrowActual hcommon hsource hfine hroot hrelative hfee hgridFine
    firstInput Daughter src J continues oldPackage childAt SourceK Control slotLoss OldPaid
  letI : Cycle63.AffineLedger:=N.ledger
  let hmu : 0<nativeMu:=nativeMu_pos
  let hlog : (∑i : N.slots,Real.logb N.localBase (s.P i))=
      ∑i : N.slots,C.originalWeight i/N.unit :=by
    apply Finset.sum_congr rfl
    intro i _
    rw [hm.scale i]
    exact Real.logb_rpow (zero_lt_one.trans N.localBase_gt_one) N.localBase_gt_one.ne'
  let hamp : nodeSourceAmp N=Cycle63.AffineLedger.amp
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell
        (∑i : N.slots,Real.logb N.localBase (s.P i)))) :=by
    rw [hlog,nodeSourceAmp_eq_native N]
  let hdel : nodeDetectorDeletion N=
      (Cycle63.AffineLedger.regionGap (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,Real.logb N.localBase (s.P i))))+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,Real.logb N.localBase (s.P i)))))/
      (6*Cycle63.AffineLedger.price)+detectorExtra :=by
    rw [hlog]
    unfold nodeDetectorDeletion
    rw [regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩]
    congr 1 <;> norm_num [detectorExtra]
  let hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)≤1/2:=
    receipted_direct_rate_le_half j
  let hq : Cycle63.AffineLedger.q=(innerStage j.val).q:=rfl
  let hcert:=by
    have hh:=actual_inner_direct_certificate N hj hgrid
      (1/1000000000000000) (nativeMu/8) (1/1000000000000000) (by
        norm_num [nativeMu,primitiveError])
    dsimp only at hh
    rw [←hlog,←hamp] at hh
    exact hh
  let hpadu : supportPadding (Fintype.card N.slots) (9/4) s.b₁ s.b₂ N.localBase≤nativeMu/8:=hpad
  let invoke:=actualInnerCanonicalInvocation hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh
  let canonical:=invoke ch Mrow (nodeSourceAmp N) omega (nativeMu/64) (9/4) (nativeMu/8) (nativeMu/8)
    (1/1000000000000000) (1/1000000000000000) (Fintype.card N.slots) gg ray
    (internalQ C.Q C.etaSeed) hP hPN Ds zs T (actualNodeLocalSourcePad (hH:=hH) N) hOwn seed hseed
    hamp hdel (by norm_num) caps.endpoints.1 hslots haff hfit hconstants
    (by positivity) (by positivity) (by
      exact add_nonneg (frequencyLoss_nonneg N.localBase 32 (nativeMu/64) N.localBase_gt_one
        (by norm_num) (by positivity)) (by positivity)) (by positivity) hpadu homega hdelta hrate
    (actual_node_canonical_scalar_gates N).1 (by
      simpa only [directNodeRate,hq,s,Cycle153Geometry.Coordinates.mu] using hcert)
    caps.endpoints.1 hT hDs width.2.2
    (by exact inf_le_left.trans C.Q_le_M) (by exact inf_le_right)
    datum second frame chi0 chi psi m hm0 hml hm2 C.fixed_small hTsource hBetaHigh hray rfl
    buffer rfl
  let completed:=canonical hzs
    (fun B _=>actual_inner_common_allowance (hH:=hH) N Cs caps ch (gg.datum.τ ray) sourceHeight B)
    u width.2.1 width.1 (by simp only [u,nativeUnit,mul_one,add_assoc]) (width.2.1.trans (by norm_num))
    N.profiles caps.profile₁ caps.profile₂
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (N.localBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using N.localBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (N.localBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using N.localBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 1)
  let package:=actualCanonicalInnerCoordinatePacket N hj s ch (gg.datum.τ ray) sourceHeight
    (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8) C.slotMesh gg
    (by norm_num) (le_refl _) caps.endpoints.1 (input_lower hH N) (input_X1 hH N) (input_X2 hH N)
    hm.scale (by simp only [omega,mul_one]) hR2 hP hfinite hgrid Ds
  have hret:=completed P hPnorm rfl constant eps Bsrc control degree boxes hIH hconstant heps hchild
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.2.1)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).val)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.1)
  obtain ⟨R,F,trace,hbound⟩:=hret
  refine ⟨R,F,?_,hbound⟩
  by_cases hF : F=emptyReturnedForest
  · exact Or.inl hF
  · rcases trace with hempty | ⟨d,hadmit,htrace⟩
    · exact False.elim (hF hempty)
    · obtain ⟨hn,z,hne,hR,hsum,hcover,hc,out,hvalue⟩:=htrace.live hF
      apply Or.inr
      let pack:=package d hn z hne R hR hsum hcover hc
      let kept:=nodeOfNativeContinuation C (nextInner j hj) N.localBase N.unit u 28
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1) N.localBase_eq st width.1
        pack.property.2.1 (((J d\R).map (originalSubsetEmbedding N.slots))) N.profiles
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
        (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
        P hPnorm rfl sourceHeight N.height N.height_nonneg
        (by intro k;obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property;rw [←hki];exact N.frequency_bound i)
        pack.val pack.property.1
      have fields:=actual_chosen_continuation_fields C (nextInner j hj) N.localBase N.unit u 28
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1) N.localBase_eq st width.1
        pack.property.2.1 (((J d\R).map (originalSubsetEmbedding N.slots))) N.profiles
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
        (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
        P hPnorm rfl sourceHeight N.height N.height_nonneg
        (by intro k;obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property;rw [←hki];exact N.frequency_bound i)
        pack.val pack.property.1
      have hunit : kept.unit=N.unit*u :=by
        exact fields.1
      have hcoords : kept.coordinates=extendCoordinates N.coordinates (nextInner j hj)
          (nativeNodeStepValues N s (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
            (gg.datum.τ ray) sourceHeight (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8)
            (commonContinuationGeometry gg (gg.datum.τ ray) sourceHeight d.1 hn)
            d.2.2.2 d.2.1.1 d.2.2.1.1 R).V
          (nativeNodeStepValues N s (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
            (gg.datum.τ ray) sourceHeight (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8)
            (commonContinuationGeometry gg (gg.datum.τ ray) sourceHeight d.1 hn)
            d.2.2.2 d.2.1.1 d.2.2.1.1 R).Red
          (nativeNodeStepValues N s (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
            (gg.datum.τ ray) sourceHeight (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8)
            (commonContinuationGeometry gg (gg.datum.τ ray) sourceHeight d.1 hn)
            d.2.2.2 d.2.1.1 d.2.2.1.1 R).ell :=by
        exact fields.2.1.trans pack.property.2.2.1
      have hrootKept : kept.presentation.mult=P.mult :=by
        exact fields.2.2.1
      have hrowKept : kept.unit*kept.state.rowWidth=N.unit*st.rowWidth :=by
        exact fields.2.2.2.1
      let paidFields:=actual_selected_paid_node_fields N reflected second s N.state.puncture 1 Mrow
        (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsRow (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside labelRow
      let fee:=actualNodeGlobalFee (hH:=hH) N epsNode rateBudget R hsum
      obtain ⟨hu,edge,hnode,hFeeEq⟩:=actual_physical_inner_edge_for_fields N hj s ch (gg.datum.τ ray) sourceHeight
        (Fintype.card N.slots) (9/4) Mrow omega (nativeMu/64) (nativeMu/8) C.slotMesh gg
        (by norm_num) (le_refl _) caps.endpoints.1 (input_lower hH N) (input_X1 hH N) (input_X2 hH N)
        hm.scale (by simp only [omega,mul_one]) hR2 hP hPN hfinite hgrid Ds ray rfl
        width.1 P hPnorm d hn z hne R hR hsum hcover hc
        p paidFields.1 (paidFields.2.1.trans (congrArg (fun x=>N.unit*x) hMrowActual))
        paidFields.2.2.1 paidFields.2.2.2.1 hcommon hsource hfine fee (hfee R hsum)
        rfl (actual_node_fee_model (hH:=hH) N epsNode rateBudget R hsum)
        (by norm_num [nativeMu,primitiveError]) hgridFine hrelative kept hunit hcoords hrootKept hrowKept
      have raw:=actual_chosen_column_scheduled_arithmetic N reflected second s N.state.puncture 1 Mrow
        (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsRow (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside labelRow epsNode rateBudget R hsum kept edge hnode hFeeEq
      exact ⟨{
        child:=kept
        unit:=hu
        root:=hrootKept.trans hroot
        constant:=constant (nextInner j hj)
        epsilon:=eps (nextInner j hj)
        control:=control (nextInner j hj)
        degree:=degree (nextInner j hj)
        output:=out
        edge:=edge
        rawWeight:=raw.1
        rawMissing:=raw.2
        value:=hvalue }⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerCanonicalReceiptedEnergy
