/- Named SAME physical Common continuation node for native Column traces.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
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
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M  ≤  H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The literal node used by native Column traces is constructed from
ONE genuine same-daughter geometry/history/mask package. The retained
prefix, profile, independent source height and original frequency height
are unchanged. There is no node energy or output selection here. -/
def actual_physical_inner_edge_for_fields
    (N : ReachableNode C j)(hj : j.val<3)
    (s : Input N.slots)(ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (n : ℕ)(b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1  ≤  b)(hcard : Fintype.card N.slots  ≤  n)(hs : s.upper  ≤  b)(hlower : 1  ≤  s.lower)
    (hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)  ≤  N.localBase^(28:ℝ))
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂))  ≤  1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)  ≤  positionMargin)
    (Ds : Finset (Ideal O))(sourceRay : RayFourExpansion.RayCharacter)
    (hcharacter : sourceCharacter=g.datum.τ sourceRay) :=
    let st:=retainedState N.localBase 28 N.localBase_gt_one (g.datum.τ sourceRay)
      (internalQ C.Q C.etaSeed) (ch.R₂*ch.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first sourceCharacter sourceHeight
    let u:=nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    fun(hwidth : st.width  ≤  u)
      (P : PrefixHighPresentation (prefixDictionary (nextInner j hj).val C.etaSeed) st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ)  ≤  C.globalBase^prefixCap (nextInner j hj).val)=>
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
    let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    fun(d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
      (row : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
        d.2.2.2 d.2.1.1 d.2.2.1.1 row≠0)
      (R : Finset N.slots)(hR : R⊆J d)
      (hsum : (∑i∈R,C.originalWeight i/N.unit)  ≤  nodeDetectorDeletion N+mesh)
      (hcover : R=J d ∨ nodeDetectorDeletion N  ≤  ∑i∈R,C.originalWeight i/N.unit)
      (hc : nativeMainContinuation N.state u (J d) R (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1))=>
    fun (p : NativePaidPathNode C.globalBase)
      (hunit : p.unit=N.unit)(hrow : p.scale=N.unit*N.state.rowWidth)
      (hvolume : p.volumeLength=N.unit*Real.logb N.localBase (volume (N.input hH)))
      (hamp : p.amplification=N.unit*nodeSourceAmp N)
      (hcommon : p.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+Real.logb N.localBase (ch.E₂.absNorm:ℝ)))
      (source : p.SourceGates)(fine : p.FineSourceGates)
      (fee : NativePathFee)(hfee : fee.amount ≤ 1/1000000000000000)
      (hq : fee.junction=(innerStage j.val).q)(hD : fee.modelDeletion=pathDeletion j.val N.coordinates)
      (hxi : xi ≤ 1/1000000000000000)
      (hgridFine : (1/C.gridDenominator:ℝ) ≤ 1/10000000000000000000000000000000000000000)
      (hrelative : N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {P.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
        N.unit*(Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2))=>
    let q:=commonContinuationChain s ch sourceCharacter sourceHeight d.1
    let gg:=commonContinuationGeometry g sourceCharacter sourceHeight d.1 hn
    let step:=nativeNodeStepValues N s q sourceCharacter sourceHeight n b Mrow omega xi reserve gg
      d.2.2.2 d.2.1.1 d.2.2.1.1 R
    fun (chosen : ReachableNode C (nextInner j hj))
      (hchosenUnit : chosen.unit=N.unit*u)
      (coordinates : chosen.coordinates=extendCoordinates N.coordinates (nextInner j hj) step.V step.Red step.ell)
      (hchosenRoot : chosen.presentation.mult=P.mult)
      (hchosenRow : chosen.unit*chosen.state.rowWidth=N.unit*st.rowWidth)=>
    show ∃hu : chosen.unit ≤ N.unit,
      ∃edge : NativeTraceEdge (hH:=hH) N chosen.coordinates
        (chosen.unit*chosen.state.rowWidth)
        (chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)))
        (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)),
      edge.node=p ∧ edge.fee=fee from by
      let q:=commonContinuationChain s ch sourceCharacter sourceHeight d.1
      let gg:=commonContinuationGeometry g sourceCharacter sourceHeight d.1 hn
      let step:=nativeNodeStepValues N s q sourceCharacter sourceHeight n b Mrow omega xi reserve gg
        d.2.2.2 d.2.1.1 d.2.2.1.1 R
      have hnStep:=actual_inner_native_node_step N s q sourceCharacter sourceHeight n b Mrow omega xi reserve mesh gg
        hb hcard hs hlower hX1 hX2 hscale d.2.2.2 d.2.1.1 d.2.2.1.1 row hne R hR hc.2.1 hcover hsum
        homega hR2 hP hfinite
      have hu1 : u ≤ 1:=by
        have hr : RawPrefixRows j N.coordinates:=by
          intro i hi _ _
          exact N.prefixRows i (by simpa only [Nat.add_assoc] using hi)
        have ha:=raw_prefix_amplifier_nonneg j N.coordinates hr
        have hamp0 : 0  ≤  modelAmplification j N.coordinates:=by fin_cases j <;> exact ha
        change 0 ≤ step.V ∧ _ at hnStep
        change step.u ≤ 1
        nlinarith only [hnStep.1,hnStep.2.2.2.1,hamp0,N.unit_pos]
      have hchildA : chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH))=step.childA:=by
        rw [chosen.volume_model,coordinates,(physical_next_models j hj N.coordinates step.V step.Red step.ell).2.1]
        exact hnStep.2.2.2.2.2.1.symm
      have hq0 : 0 ≤ fee.junction:=by rw [hq];exact (innerStage j.val).q_pos.le
      have hq1 : fee.junction ≤ 1:=by rw [hq];exact (innerStage j.val).q_le_price.trans (innerStage j.val).price_le_one
      have hdel : pathDeletion j.val N.coordinates ≤ 1:=by
        have hd : pathDeletion j.val N.coordinates/N.unit ≤ ∑i∈R,C.originalWeight i/N.unit:=by
          have hcover':=hcover.resolve_left hc.2.1
          have hh:=(nodeDetectorDeletion_bounds N).1
          linarith only [hcover',hh]
        have ht : (∑i∈R,C.originalWeight i/N.unit) ≤ 1:=by
          have hsumAll : (∑i∈R,C.originalWeight i/N.unit) ≤ ∑i : N.slots,C.originalWeight i/N.unit:=by
            apply Finset.sum_le_univ_sum_of_nonneg
            intro i
            exact div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le
          exact hsumAll.trans (N.window.slots_le.trans N.positionFacts.slotTop_le_one)
        have hg:=mul_le_mul_of_nonneg_left (hd.trans ht) N.unit_pos.le
        rw [mul_div_cancel₀ _ N.unit_pos.ne',mul_one] at hg
        exact hg.trans N.unit_le_one
      have hremaining : fee.junction*fee.modelDeletion+fee.amount ≤ 2:=by
        rw [hD]
        have h1:=mul_le_mul_of_nonneg_left hdel hq0
        norm_num only [mul_one] at h1
        linarith only [h1,hq1,hfee]
      have hpad : N.unit*(Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2) ≤ 1/1000000000000:=by
        have hlog : Real.logb N.localBase 4 ≤ Real.logb N.localBase 128:=
          (Real.logb_le_logb N.localBase_gt_one (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<128)).2 (by norm_num)
        have hbits : 0 ≤ 252*(1/C.gridDenominator:ℝ):=by positivity
        have hends : 0 ≤ Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂):=by
          apply Real.logb_nonneg N.localBase_gt_one
          exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
        have hp : Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2 ≤ 1/1000000000000000:=by
          linarith only [hlog,hbits,hends,hfinite,hxi]
        have hh:=mul_le_mul_of_nonneg_left hp N.unit_pos.le
        nlinarith only [hh,N.unit_le_one]
      have hrelativeChosen : chosen.unit*chosen.state.rowWidth+
          Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)-
          Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
          N.unit*(Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2):=by
        rw [hchosenRow,hchosenRoot]
        exact hrelative
      let edge:=actual_inner_native_trace_edge N hj s q sourceCharacter sourceHeight n b Mrow omega xi reserve mesh gg
        hb hcard hs hlower hX1 hX2 hscale d.2.2.2 d.2.1.1 d.2.2.1.1 row hne R hR hc.2.1 hcover hsum
        homega hR2 hP hfinite p hunit hrow hvolume hamp hcommon source fine fee
        (by linarith only [hfee]) hremaining hq hD (chosen.unit*chosen.state.rowWidth)
        (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ))
        (N.unit*(Real.logb N.localBase 4+2*(n:ℝ)*Real.logb N.localBase b+xi/2)) hpad hrelativeChosen hgridFine
      refine ⟨?_,edge.reindex coordinates hchildA,?_,?_⟩
      · rw [hchosenUnit]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 N.unit_pos.le
      · exact (edge.reindex_node coordinates hchildA).trans rfl
      · exact (edge.reindex_fee coordinates hchildA).trans rfl


end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_physical_inner_edge_for_fields

