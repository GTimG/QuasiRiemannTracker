/- The actual bare-root selected source child and its SAME priced edge. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeActualRootSourceChild
import Candidate.Research.RecursiveAffine.ActualRootNativeFee
import Candidate.Research.RecursiveAffine.ActualTraceTerminal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
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
open CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn CenteredMomentNaturalRowSource
open CenteredMomentDivisorAllocation Cycle153ReachableGeometry CenteredMomentEnergyBands
open Cycle153HighProvider Cycle153JointCount Cycle153RegionalLow Cycle153ContinuationUnit
open Cycle153RootStep Cycle153Geometry CenteredMomentFiniteProfileExceptional
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}
noncomputable local instance actualRootSourceEdgeLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- Attach the literal native capacity/scale price to the SAME constructed
first inner node. The native volume-majorant lift compensates massLoss
exactly; raw source length is not identified with the model plane. -/
theorem actual_root_selected_source_child_edge
    (s : Input alpha)(F0 : NaturalRow C.etaSeed 1)(R0 : Ideal O)
    (hparent : ParentPresentation s.η F0 R0)
    (p : Profiles (1/4) (9/4))
    (reflected second : Bool)(xi reserve b firstHeight eps : ℝ)(budget : ℕ)
    (hamp : 0 ≤ rootSourceAmp C.originalWeight)
    (hloss : 0 ≤ frequencyLoss C.globalBase 32 xi+reserve)
    (heps0 : 0 ≤ eps)(heps : eps ≤ 1)(hb : 0<b)
    (hsmall : Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2 ≤ 1)
    (hsource : sourceRadius s ≤ C.globalBase^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin)
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      xi reserve b firstHeight budget C.globalBase_gt_one bin q) :
    let datum:=geometryLowSecondDatum reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      xi reserve b firstHeight budget C.globalBase_gt_one bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin firstHeight q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s 1 1 (C.globalBase^(1:ℝ))
        C.globalBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin q.1.val)
        1 s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C) datum.R src.ν src.W src.P≠0)
      (chi : RayCharacter)(Bmask sourceHeight : ℝ),
    let chain:=geometryLowActualChain reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      xi reserve b firstHeight budget C.globalBase_gt_one bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      xi reserve b firstHeight budget C.globalBase_gt_one bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0)(hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ C.globalBase^Bmask),
    let st:=retainedState C.globalBase Bmask C.globalBase_gt_one (g.datum.τ chi) (internalQ C.Q C.etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin q.1.val
    let label:=Cycle63InitialMass.actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    let units:=fun l=>(firstDictionaryUnit (!reflected) C.etaSeed 1 F0 R0 l:O)
    ∀(hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
      (hwindow : Cycle63.AffineLedger.PlainWindow
        (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
      (hcard : Fintype.card alpha ≤ budget)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)(hb1 : 1 ≤ b)
      (hR2 : chain.R₂=(1:Ideal O)*chain.C₁)
      (hfit : Real.logb C.globalBase (s.η.modulus.absNorm:ℝ) ≤ reserve/2)
      (hconstants : Real.logb C.globalBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(budget:ℝ)*Real.logb C.globalBase b+Real.logb C.globalBase 1+
        Real.logb C.globalBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ reserve/2)
      (mesh : ℝ)(secondResidual : Bool)(L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset
        ((CenteredMomentCommonProfile.liveIndices chain.B₂.val)⊕Fin 2)))
      (liveRow : O)
      (hne : Cycle63.Physical.sourcePositiveRow (chain.final (g.datum.τ chi) sourceHeight).toSource
        secondResidual L alloc liveRow≠0)
      (Rdel : Finset alpha)(hRdel : Rdel ⊆ chain.indices L alloc)(hproper : Rdel≠chain.indices L alloc)
      (hcover : Rdel=chain.indices L alloc ∨ rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)
      (hdelmesh : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh)
      (hfinite : Real.logb C.globalBase 128+(2*(budget:ℝ)*Real.logb C.globalBase b+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000),
    let omega:=frequencyLoss C.globalBase 32 xi+reserve
    let step:=nativeRootStepValues s chain (g.datum.τ chi) sourceHeight C.globalBase budget b 1 omega xi reserve
      C.originalWeight g secondResidual L alloc Rdel
    ∀(hcontinue : nativeMainContinuation st step.u (chain.indices L alloc) Rdel C.originalWeight
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1))
      (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
      (height : ℝ)(hheight : 0 ≤ height)(hfreq : ∀i,|C.frequency i| ≤ height),
    ∀(praw : NativePaidPathNode C.globalBase)
      (hunit : praw.unit=1)(hrow : praw.scale ≤ 1)
      (hlength : praw.length=Real.logb C.globalBase (volume s))
      (hampActual : praw.amplification=rootSourceAmp C.originalWeight)
      (hcommon : praw.commonLog=Real.logb C.globalBase (chain.C₁.absNorm:ℝ)+
        Real.logb C.globalBase (chain.E₂.absNorm:ℝ))
      (hcoord2 : praw.coordinate 2=actualHighCoordinates reflected (!reflected) second first
        datum.C datum.D datum.inactive C.globalBase 1 (Real.logb C.globalBase (volume s))
        (rootSourceAmp C.originalWeight) xi reserve eps 2)
      (source : praw.SourceGates)(fine : praw.FineSourceGates)
      (fee : NativePathFee)(hfee : fee.amount ≤ 1/1000000000000000)
      (hq : fee.junction=Coordinates.q0)(hD : fee.modelDeletion=rootSourceDeletion C.originalWeight)
      (hxi : xi ≤ 1/1000000000000000),
    ∃child : ReachableNode C 0,
      child.unit=step.u ∧ child.unit ≤ 1 ∧
      child.coordinates=rootCoordinates step.b step.rootSlack step.V step.Red step.ell ∧
      child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) 1 units ⟨first,label⟩ ∧
      child.unit*child.state.rowWidth=st.rowWidth ∧
      ∃edge : RootTraceEdge (C:=C) child.coordinates
        (child.unit*child.state.rowWidth)
        (child.unit*Real.logb child.localBase (volume (child.input hH)))
        (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)),
        edge.node=praw.lengthLift (rootSourceLength C.originalWeight-praw.length) ∧ edge.fee=fee :=by
  intro datum src allocation r hf1 hf2 chi Bmask sourceHeight chain g hP hPN st first label units
  intro hscale hwindow hcard hs hlower hb1 hR2 hfit hconstants mesh secondResidual L alloc liveRow hne
  intro Rdel hRdel hproper hcover hdelmesh hfinite omega step hcontinue hgrid height hheight hfreq
  intro praw hunit hrow hlength hampActual hcommon hcoord2 source fine fee hfee hq hD hxi
  obtain ⟨child,hcu,hcle,hcoords,hroot,hrowscale,hrelative⟩:=actual_root_selected_source_child
    s F0 R0 hparent p reflected second xi reserve b firstHeight eps budget hamp hloss heps0 heps hb hsmall hsource
    bin q hz1 hz2 n allocation r hf1 hf2 chi Bmask sourceHeight hP hPN hscale hwindow hcard hs hlower hb1 hR2 hfit
    hconstants mesh secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh hfinite
    hcontinue hgrid height hheight hfreq
  have hn:=actual_outer_native_root_step s chain (g.datum.τ chi) sourceHeight C.globalBase C.globalBase_gt_one
    budget b 1 omega xi reserve mesh C.originalWeight g hb1 hcard hs hlower C.originalWeight_nonneg hscale
    hwindow secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite
  let x:=rootCoordinates step.b step.rootSlack step.V step.Red step.ell
  have hAmodel:=root_length_model_alias C.originalWeight x rfl rfl
  have hDmodel:=root_deletion_model_alias C.originalWeight x rfl
  have hchildA : child.unit*Real.logb child.localBase (volume (child.input hH))=step.childA :=by
    rw [child.volume_model,hcoords]
    change Coordinates.A0 x-Coordinates.d0 x-step.V-step.Red=step.childA
    rw [←hAmodel.1,←hDmodel]
    exact hn.2.2.2.2.2.2.2.2.2.2.1.symm
  have hq0 : 0 ≤ fee.junction :=by rw [hq];norm_num [Coordinates.q0]
  have hq1 : fee.junction ≤ 1 :=by rw [hq];norm_num [Coordinates.q0]
  have hdel : rootSourceDeletion C.originalWeight ≤ 1 :=by
    have hcover':=hcover.resolve_left hproper
    unfold rootDetectorDeletion at hcover'
    have hsum : (∑i∈Rdel,C.originalWeight i) ≤ ∑i,C.originalWeight i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>C.originalWeight_nonneg i)
    have htop:=hwindow.slots_le.trans Cycle63.AffineLedger.slotTop_le_one
    norm_num only at hcover'
    linarith only [hcover',hsum,htop]
  have hremaining : fee.junction*fee.modelDeletion+fee.amount ≤ 2 :=by
    rw [hD]
    have hh:=mul_le_mul_of_nonneg_left hdel hq0
    norm_num only [mul_one] at hh
    linarith only [hh,hq1,hfee]
  have hpadR : Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2 ≤
      1/1000000000000 :=by
    have hlog : Real.logb C.globalBase 4 ≤ Real.logb C.globalBase 128 :=
      (Real.logb_le_logb C.globalBase_gt_one (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<128)).2 (by norm_num)
    have hends : 0 ≤ Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂) :=by
      apply Real.logb_nonneg C.globalBase_gt_one
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    linarith only [hlog,hends,hfinite,hxi]
  have hrel : child.unit*child.state.rowWidth+
      Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ) ≤ praw.coordinate 2+
      (Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2) :=by
    rw [hcoord2]
    exact hrelative
  let edge:=actual_root_native_trace_edge s chain (g.datum.τ chi) sourceHeight budget b 1 omega xi reserve mesh g
    hb1 hcard hs hlower hscale hwindow secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite praw hunit hrow hlength hampActual hcommon source fine fee
    (by linarith only [hfee]) hremaining hq hD (child.unit*child.state.rowWidth)
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
    (Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2) hpadR hrel
  refine ⟨child,hcu,hcle,hcoords,hroot,hrowscale,?_⟩
  rw [hcoords,hchildA]
  exact ⟨edge,rfl,rfl⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_selected_source_child_edge
