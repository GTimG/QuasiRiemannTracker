/- Named SAME physical Common continuation node for native Column traces.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalInnerCoordinatePacket
import Candidate.Research.RecursiveAffine.NativeChosenContinuationFields

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
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The literal node used by native Column traces is constructed from
ONE genuine same-daughter geometry/history/mask package. The retained
prefix, profile, independent source height and original frequency height
are unchanged. There is no node energy or output selection here. -/
def actual_inner_column_literal_fields
    (N : ReachableNode C j)(hj : j.val<3)
    (s : Input N.slots)(ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (n : ℕ)(b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b)(hcard : Fintype.card N.slots ≤ n)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)
    (hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ N.localBase^(28:ℝ))
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (Ds : Finset (Ideal O))(sourceRay : RayFourExpansion.RayCharacter)
    (hcharacter : sourceCharacter=g.datum.τ sourceRay) :=
    let st:=retainedState N.localBase 28 N.localBase_gt_one (g.datum.τ sourceRay)
      (internalQ C.Q C.etaSeed) (ch.R₂*ch.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first sourceCharacter sourceHeight
    let u:=nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    fun(hwidth : st.width ≤ u)
      (P : PrefixHighPresentation (prefixDictionary (nextInner j hj).val C.etaSeed) st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^prefixCap (nextInner j hj).val)=>
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
    let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    fun(d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
      (row : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
        d.2.2.2 d.2.1.1 d.2.2.1.1 row≠0)
      (R : Finset N.slots)(hR : R⊆J d)
      (hsum : (∑i∈R,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
      (hcover : R=J d ∨ nodeDetectorDeletion N ≤ ∑i∈R,C.originalWeight i/N.unit)
      (hc : nativeMainContinuation N.state u (J d) R (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1))=>
    let packet:=actualCanonicalInnerDaughterPackage N hj s ch sourceCharacter sourceHeight n b Mrow omega xi
      reserve mesh g hb hcard hs hlower hX1 hX2 hscale homega hR2 hP hfinite hgrid Ds
      d hn row hne R hR hsum hcover hc
  actual_chosen_continuation_fields C (nextInner j hj) N.localBase N.unit u 28
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1) N.localBase_eq st hwidth packet.property.2
    (((J d\R).map (originalSubsetEmbedding N.slots))) N.profiles
    (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
    (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (raw_daughter_scale_pos (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)
    P hPnorm rfl sourceHeight N.height N.height_nonneg
    (by intro k;obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property;rw [←hki];exact N.frequency_bound i)
    packet.val packet.property.1


end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_inner_column_literal_fields

