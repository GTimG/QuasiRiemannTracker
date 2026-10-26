/- Literal live LOW source to its SAME reachable child. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeActualChild
import Candidate.Research.RecursiveAffine.ActualNativePrefix
import Candidate.Research.RecursiveAffine.NativeMappedChildIH
import Candidate.Research.RecursiveAffine.NativePhysicalEdge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 700000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondInputCapacitySource Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation Cycle153ReachableGeometry
open Cycle153HighProvider Cycle153JointCount Cycle153RegionalLow Cycle153ContinuationUnit
variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Reindex only dependent coordinate/volume indices of the SAME edge. -/
def NativeTraceEdge.reindex {N : ReachableNode C j}{x y : Fin 14→ℝ}{m A A' logPrefix : ℝ}
    (edge : NativeTraceEdge (hH:=hH) N x m A logPrefix)(hx : y=x)(hA : A'=A) :
    NativeTraceEdge (hH:=hH) N y m A' logPrefix :=by
  cases hx
  cases hA
  exact edge

@[simp] theorem NativeTraceEdge.reindex_node {N : ReachableNode C j}{x y : Fin 14→ℝ}{m A A' logPrefix : ℝ}
    (edge : NativeTraceEdge (hH:=hH) N x m A logPrefix)(hx : y=x)(hA : A'=A) :
    (edge.reindex hx hA).node=edge.node :=by
  cases hx
  cases hA
  rfl

@[simp] theorem NativeTraceEdge.reindex_fee {N : ReachableNode C j}{x y : Fin 14→ℝ}{m A A' logPrefix : ℝ}
    (edge : NativeTraceEdge (hH:=hH) N x m A logPrefix)(hx : y=x)(hA : A'=A) :
    (edge.reindex hx hA).fee=edge.fee :=by
  cases hx
  cases hA
  rfl

/-- Invoke the literal native prefix, width and geometry theorems at the
actual selected first/second allocation and residual detector deletion.
The first-column height and the independent final-source height are separately quantified.
The source character, radial, puncture, inherited original slots, moving
height and exact root multiplier are retained. No next-source bound or
energy estimate is an input. -/
theorem actual_selected_source_child (N : ReachableNode C j) (hj : j.val<3)
    (s : Input N.slots) (R : Ideal O)
    (P0 : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) s.η R)
    (hP0mult : P0.mult=N.presentation.mult)
    (reflected second : Bool) (Mrow xi reserve b firstHeight sourceHeight eps : ℝ) (budget : ℕ)
    (hMrow : Mrow ≤ 2) (hamp : 0 ≤ (nodeSourceAmp N)) (hloss : 0 ≤ frequencyLoss N.localBase 32 xi+reserve)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1) (hb : 0<b)
    (hsmall : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2 ≤ 1)
    (hsource : sourceRadius s ≤ N.localBase^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R 1
      (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve
      b firstHeight budget N.localBase_gt_one bin q) :
    let datum:=geometryLowSecondDatum reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin firstHeight q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R 1
        (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
        bin q.1.val) R s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ N.localBase^Bmask),
    let st:=retainedState N.localBase Bmask N.localBase_gt_one (g.datum.τ chi) (internalQ C.Q C.etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    ∀(hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
      (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
      (hcard : Fintype.card N.slots ≤ budget)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)
      (hb1 : 1 ≤ b)(hR2 : chain.R₂=N.state.puncture*chain.C₁)
      (hfit : Mrow+Real.logb N.localBase (s.η.modulus.absNorm:ℝ) ≤ 1+reserve/2)
      (hconstants : Real.logb N.localBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(budget:ℝ)*Real.logb N.localBase b+Real.logb N.localBase 1+
        Real.logb N.localBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ reserve/2)
      (mesh : ℝ)
      (secondResidual : Bool)(L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset
        ((CenteredMomentCommonProfile.liveIndices chain.B₂.val)⊕Fin 2)))
      (liveRow : O)
      (hne : Cycle63.Physical.sourcePositiveRow (chain.final (g.datum.τ chi) sourceHeight).toSource
        secondResidual L alloc liveRow≠0)
      (Rdel : Finset N.slots)(hRdel : Rdel ⊆ chain.indices L alloc)
      (hproper : Rdel≠chain.indices L alloc)
      (hcover : Rdel=chain.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
      (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
      (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
        (2*(budget:ℝ)*Real.logb N.localBase b+
          Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000),
    let omega:=frequencyLoss N.localBase 32 xi+reserve
    let step:=nativeNodeStepValues N s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve
      g secondResidual L alloc Rdel
    ∀(hcontinue : nativeMainContinuation N.state step.u (chain.indices L alloc) Rdel
      (fun i=>C.originalWeight i/N.unit)
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1))
      (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin),
    ∃child : ReachableNode C (nextInner j hj),
      child.unit=N.unit*step.u ∧ child.unit ≤ N.unit ∧
      child.coordinates=extendCoordinates N.coordinates (nextInner j hj) step.V step.Red step.ell ∧
      child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) P0.mult (P0.unit (!reflected)) ⟨first,label⟩ ∧
      child.unit*child.state.rowWidth=N.unit*st.rowWidth ∧
      child.unit*child.state.rowWidth+Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤
        N.unit*actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          N.localBase Mrow (Real.logb N.localBase (volume s)) (nodeSourceAmp N) xi reserve eps 2+
        N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label
  intro hX1 hX2 hscale hcard hs hlower hb1 hR2 hfit hconstants mesh secondResidual L alloc liveRow hne
  intro Rdel hRdel hproper hcover hdelmesh hfinite omega step hcontinue hgrid
  obtain ⟨Next,hmult,hcap,hrelative⟩:=actual_native_continuation_prefix N s R P0 hP0mult
    reflected second Mrow (nodeSourceAmp N) xi reserve b firstHeight eps budget hMrow hamp hloss heps0 heps hb hsmall
    hsource bin q hz1 hz2 n allocation r hf1 hf2 chi Bmask hP hPN
  have hwidth:=actual_native_unit (U:=1) g Bmask N.localBase_gt_one hb chi
    (internalQ C.Q C.etaSeed) hP hPN (by simpa only [mul_one,div_mul_eq_mul_div] using hfit)
    (by simpa only [mul_one] using hconstants) (by simp only [omega,mul_one])
  let geom:=actual_inner_native_child_package N hj s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve
    mesh g hb1 hcard hs hlower hX1 hX2 hscale secondResidual L alloc liveRow hne Rdel hRdel hproper
    hcover hdelmesh (by simp only [omega,mul_one]) hR2 hP hfinite hcontinue hgrid
  have hwide : (397/1000:ℝ) ≤ step.u:=hcontinue.1
  have hu : 0<step.u:=lt_of_lt_of_le (by norm_num) hwide
  have hu1 : step.u ≤ 1 := by
    have hn:=actual_inner_native_node_step N s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve
      mesh g hb1 hcard hs hlower hX1 hX2 hscale secondResidual L alloc liveRow hne Rdel hRdel hproper
      hcover hdelmesh (by simp only [omega,mul_one]) hR2 hP hfinite
    have hamp0 : 0 ≤ modelAmplification j N.coordinates := by
      have hr : RawPrefixRows j N.coordinates:=by
        intro i hi _ _
        exact N.prefixRows i (by simpa only [Nat.add_assoc] using hi)
      have ha:=raw_prefix_amplifier_nonneg j N.coordinates hr
      fin_cases j <;> exact ha
    change 0 ≤ step.V ∧ _ at hn
    nlinarith only [hn.1,hn.2.2.2.1,hamp0,N.unit_pos]
  have hw : st.width ≤ step.u:=hwidth.1
  let child:=nodeOfNativeContinuation C (nextInner j hj) N.localBase N.unit step.u Bmask hu N.localBase_eq st hw
    geom.2.2 (nativeSurvivingSlots N.slots (chain.indices L alloc) Rdel) N.profiles
    (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)
    (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)
    (raw_daughter_scale_pos _ _ _ _ 0) (raw_daughter_scale_pos _ _ _ _ 1)
    Next hcap rfl sourceHeight N.height N.height_nonneg
    (fun i=>N.frequency_bound ⟨i.val,nativeSurvivingSlots_subset N.slots
      (chain.indices L alloc) Rdel i.property⟩) geom.1 geom.2.1
  have hrowscale : child.unit*child.state.rowWidth=N.unit*st.rowWidth := by
    change (N.unit*step.u)*(nativeContinuationState st step.u hu hw geom.2.2).rowWidth=_
    exact native_continuation_global_row_scale st N.unit step.u hu hw geom.2.2
  refine ⟨child,rfl,?_,?_,?_,hrowscale,?_⟩
  · change N.unit*step.u ≤ N.unit
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 N.unit_pos.le
  · change geom.val.coordinates=_
    rfl
  · change Next.mult=_
    exact hmult
  · rw [hrowscale]
    change N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ)-_ ≤ _
    rw [←hP0mult]
    exact hrelative

/-- The actual selected source child carries the priced native edge, using
its literal prefix and source capacity; no trace/payment conclusion is assumed. -/
theorem actual_selected_source_child_edge (N : ReachableNode C j) (hj : j.val<3)
    (s : Input N.slots) (R : Ideal O)
    (P0 : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) s.η R)
    (hP0mult : P0.mult=N.presentation.mult)
    (reflected second : Bool) (Mrow xi reserve b firstHeight sourceHeight eps : ℝ) (budget : ℕ)
    (hMrow : Mrow ≤ 2) (hamp : 0 ≤ (nodeSourceAmp N)) (hloss : 0 ≤ frequencyLoss N.localBase 32 xi+reserve)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1) (hb : 0<b)
    (hsmall : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2 ≤ 1)
    (hsource : sourceRadius s ≤ N.localBase^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R 1
      (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve
      b firstHeight budget N.localBase_gt_one bin q) :
    let datum:=geometryLowSecondDatum reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin firstHeight q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R 1
        (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
        bin q.1.val) R s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s R 1 N.localBase Mrow (nodeSourceAmp N) xi reserve b firstHeight
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ N.localBase^Bmask),
    let st:=retainedState N.localBase Bmask N.localBase_gt_one (g.datum.τ chi) (internalQ C.Q C.etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    ∀(hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
      (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
      (hcard : Fintype.card N.slots ≤ budget)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)
      (hb1 : 1 ≤ b)(hR2 : chain.R₂=N.state.puncture*chain.C₁)
      (hfit : Mrow+Real.logb N.localBase (s.η.modulus.absNorm:ℝ) ≤ 1+reserve/2)
      (hconstants : Real.logb N.localBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(budget:ℝ)*Real.logb N.localBase b+Real.logb N.localBase 1+
        Real.logb N.localBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ reserve/2)
      (mesh : ℝ)
      (secondResidual : Bool)(L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset
        ((CenteredMomentCommonProfile.liveIndices chain.B₂.val)⊕Fin 2)))
      (liveRow : O)
      (hne : Cycle63.Physical.sourcePositiveRow (chain.final (g.datum.τ chi) sourceHeight).toSource
        secondResidual L alloc liveRow≠0)
      (Rdel : Finset N.slots)(hRdel : Rdel ⊆ chain.indices L alloc)
      (hproper : Rdel≠chain.indices L alloc)
      (hcover : Rdel=chain.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
      (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
      (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
        (2*(budget:ℝ)*Real.logb N.localBase b+
          Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000),
    let omega:=frequencyLoss N.localBase 32 xi+reserve
    let step:=nativeNodeStepValues N s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve
      g secondResidual L alloc Rdel
    ∀(hcontinue : nativeMainContinuation N.state step.u (chain.indices L alloc) Rdel
      (fun i=>C.originalWeight i/N.unit)
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1))
      (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin),
    ∀(p : NativePaidPathNode C.globalBase)
      (hunit : p.unit=N.unit)(hrow : p.scale=N.unit*N.state.rowWidth)
      (hMrowActual : Mrow=N.state.rowWidth)
      (hvolume : p.volumeLength=N.unit*Real.logb N.localBase (volume (N.input hH)))
      (hampActual : p.amplification=N.unit*nodeSourceAmp N)
      (hcommon : p.commonLog=N.unit*(Real.logb N.localBase (chain.C₁.absNorm:ℝ)+
        Real.logb N.localBase (chain.E₂.absNorm:ℝ)))
      (hcoord2 : p.coordinate 2=N.unit*actualHighCoordinates reflected (!reflected) second first
        datum.C datum.D datum.inactive N.localBase Mrow (Real.logb N.localBase (volume s))
        (nodeSourceAmp N) xi reserve eps 2)
      (source : p.SourceGates)(fine : p.FineSourceGates)
      (fee : NativePathFee)(hfee : fee.amount ≤ 1/1000000000000000)
      (hq : fee.junction=(innerStage j.val).q)
      (hD : fee.modelDeletion=pathDeletion j.val N.coordinates)
      (hxi : xi ≤ 1/1000000000000000)
      (hgridFine : (1/C.gridDenominator:ℝ) ≤ 1/10000000000000000000000000000000000000000),
    ∃child : ReachableNode C (nextInner j hj),
      child.unit=N.unit*step.u ∧ child.unit ≤ N.unit ∧
      child.coordinates=extendCoordinates N.coordinates (nextInner j hj) step.V step.Red step.ell ∧
      child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) P0.mult (P0.unit (!reflected)) ⟨first,label⟩ ∧
      child.unit*child.state.rowWidth=N.unit*st.rowWidth ∧
      ∃edge : NativeTraceEdge (hH:=hH) N child.coordinates
        (child.unit*child.state.rowWidth)
        (child.unit*Real.logb child.localBase (volume (child.input hH)))
        (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)),
      edge.node=p ∧ edge.fee=fee := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label
  intro hX1 hX2 hscale hcard hs hlower hb1 hR2 hfit hconstants mesh secondResidual L alloc liveRow hne
  intro Rdel hRdel hproper hcover hdelmesh hfinite omega step hcontinue hgrid
  intro p hunit hrow hMrowActual hvolume hampActual hcommon hcoord2 source fine fee hfee hq hD hxi hgridFine
  obtain ⟨child,hcu,hcle,hcoords,hroot,hrowscale,hrelative⟩:=actual_selected_source_child N hj s R P0 hP0mult
    reflected second Mrow xi reserve b firstHeight sourceHeight eps budget hMrow hamp hloss heps0 heps hb hsmall hsource bin q hz1 hz2 n
    allocation r hf1 hf2 chi Bmask hP hPN hX1 hX2 hscale hcard hs hlower hb1 hR2 hfit hconstants mesh
    secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh hfinite hcontinue hgrid
  have hn:=actual_inner_native_node_step N s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve mesh g
    hb1 hcard hs hlower hX1 hX2 hscale secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite
  have hchildA : child.unit*Real.logb child.localBase (volume (child.input hH))=step.childA := by
    rw [child.volume_model,hcoords,(physical_next_models j hj N.coordinates step.V step.Red step.ell).2.1]
    exact hn.2.2.2.2.2.1.symm
  have hq0 : 0 ≤ fee.junction :=by rw [hq];exact (innerStage j.val).q_pos.le
  have hq1 : fee.junction ≤ 1 :=by
    rw [hq];exact (innerStage j.val).q_le_price.trans (innerStage j.val).price_le_one
  have hdel : pathDeletion j.val N.coordinates ≤ 1 :=by
    have hd : pathDeletion j.val N.coordinates/N.unit ≤ ∑i∈Rdel,C.originalWeight i/N.unit :=by
      have hcover':=hcover.resolve_left hproper
      have hh:=(nodeDetectorDeletion_bounds N).1
      linarith only [hcover',hh]
    have hsum : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ ∑i : N.slots,C.originalWeight i/N.unit :=by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro i
      exact div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le
    have htop : (∑i : N.slots,C.originalWeight i/N.unit) ≤ 1 :=
      N.window.slots_le.trans N.positionFacts.slotTop_le_one
    have hg:=mul_le_mul_of_nonneg_left (hd.trans (hsum.trans htop)) N.unit_pos.le
    rw [mul_div_cancel₀ _ N.unit_pos.ne',mul_one] at hg
    exact hg.trans N.unit_le_one
  have hremaining : fee.junction*fee.modelDeletion+fee.amount ≤ 2 :=by
    rw [hD]
    have h1:=mul_le_mul_of_nonneg_left hdel hq0
    norm_num only [mul_one] at h1
    linarith only [h1,hq1,hfee]
  have hpadR : N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) ≤
      1/1000000000000 :=by
    have hlog : Real.logb N.localBase 4≤Real.logb N.localBase 128 :=
      (Real.logb_le_logb N.localBase_gt_one (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<128)).2 (by norm_num)
    have hbits : 0 ≤ 252*(1/C.gridDenominator:ℝ) :=by positivity
    have hends : 0 ≤ Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂) :=by
      apply Real.logb_nonneg N.localBase_gt_one
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    have hp : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2 ≤
        1/1000000000000000 :=by linarith only [hlog,hbits,hends,hfinite,hxi]
    have hh:=mul_le_mul_of_nonneg_left hp N.unit_pos.le
    nlinarith only [hh,N.unit_le_one]
  have hrel : child.unit*child.state.rowWidth+
      Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)-
      Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+
      N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) :=by
    rw [hcoord2]
    exact hrelative
  let edge:=actual_inner_native_trace_edge N hj s chain (g.datum.τ chi) sourceHeight budget b Mrow omega xi reserve mesh g
    hb1 hcard hs hlower hX1 hX2 hscale secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite p hunit hrow hvolume hampActual hcommon source fine fee
    (by linarith only [hfee]) hremaining hq hD (child.unit*child.state.rowWidth)
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
    (N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2)) hpadR hrel hgridFine
  let edge':=edge.reindex hcoords hchildA
  refine ⟨child,hcu,hcle,hcoords,hroot,hrowscale,edge',?_,?_⟩
  · exact (edge.reindex_node hcoords hchildA).trans rfl
  · exact (edge.reindex_fee hcoords hchildA).trans rfl


end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_selected_source_child

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_selected_source_child_edge
