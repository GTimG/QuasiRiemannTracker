/- Literal bare-root LOW source to its SAME first reachable child. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPrefix
import Candidate.Research.RecursiveAffine.NativeActualChild
import Candidate.Research.RecursiveAffine.NativeRootMask
import Candidate.Research.RecursiveAffine.NativeRootStepWidth
import Candidate.Research.RecursiveAffine.NativeRootPhysicalEdge
import Candidate.Research.RecursiveAffine.NativeMappedChildIH
import Candidate.Research.RecursiveAffine.NativeStrictLowStep

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

noncomputable local instance actualRootChildLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- Construct the first inner state directly from the actual root's
native two-ray prefix, SAME selected allocation, residual deletion and
continuation tests. No inner parent or recursive source estimate is used. -/
theorem actual_root_selected_source_child
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
    ∃child : ReachableNode C 0,
      child.unit=step.u ∧ child.unit ≤ 1 ∧
      child.coordinates=rootCoordinates step.b step.rootSlack step.V step.Red step.ell ∧
      child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) 1 units ⟨first,label⟩ ∧
      child.unit*child.state.rowWidth=st.rowWidth ∧
      child.unit*child.state.rowWidth+Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ) ≤
        actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          C.globalBase 1 (Real.logb C.globalBase (volume s)) (rootSourceAmp C.originalWeight) xi reserve eps 2+
        (Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2) :=by
  intro datum src allocation r hf1 hf2 chi Bmask sourceHeight chain g hP hPN st first label units
  intro hscale hwindow hcard hs hlower hb1 hR2 hfit hconstants mesh secondResidual L alloc liveRow hne
  intro Rdel hRdel hproper hcover hdelmesh hfinite omega step hcontinue hgrid height hheight hfreq
  obtain ⟨Next,hmult,hcap,hrelative⟩:=actual_root_native_prefix C.etaSeed F0 R0 s hparent C.globalBase
    C.globalBase_gt_one C.Q reflected second 1 (rootSourceAmp C.originalWeight) xi reserve b firstHeight eps budget
    (by norm_num) hamp hloss heps0 heps hb hsmall hsource bin q hz1 hz2 n allocation r hf1 hf2 chi Bmask hP hPN
  have hwidth:=actual_root_native_width s chain chi sourceHeight C.globalBase C.globalBase_gt_one budget b omega xi reserve
    Bmask C.originalWeight g hb (internalQ C.Q C.etaSeed) hP hPN hfit
    (by simpa only [mul_one] using hconstants) (by simp only [omega,mul_one]) secondResidual L alloc Rdel
  have hDec : Cycle153RegionalLow.strictCurrentDecidableEq (Current:=alpha)=
      (inferInstance : DecidableEq alpha):=Subsingleton.elim _ _
  have hdiff : @sdiff (Finset alpha) (@Finset.instSDiff alpha
      (Cycle153RegionalLow.strictCurrentDecidableEq (Current:=alpha))) (chain.indices L alloc) Rdel=
      chain.indices L alloc\Rdel:=native_sdiff_decEq _ _ (chain.indices L alloc) Rdel
  have hm:=hcontinue
  simp only [nativeMainContinuation,hdiff] at hm
  have hnotOld : step.u < length C.globalBase
      (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)+
      length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)+
      6*Cycle63.Optimization.slotPrice*(∑i : ↥(chain.indices L alloc\Rdel),C.originalWeight i) :=by
    simpa only [Finset.sum_coe_sort] using hm.2.2.1
  have hnotReflect :
      ¬(length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)+
        length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(chain.indices L alloc\Rdel),C.originalWeight i) ≤ step.u+19/5000 ∧
      (max 0 (step.u-length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)+1/10000)+
        length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(chain.indices L alloc\Rdel),C.originalWeight i)+19/5000 ≤ step.u ∨
       max 0 (step.u-length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)+1/10000)+
        length C.globalBase (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(chain.indices L alloc\Rdel),C.originalWeight i)+19/5000 ≤ step.u)) :=by
    simpa only [Finset.sum_coe_sort] using hm.2.2.2
  let geom:=rootGeometryOfActualNativeContinuation C s chain (g.datum.τ chi) sourceHeight budget b omega xi reserve mesh g
    hb1 hcard hs hlower hscale hwindow secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite hgrid hcontinue.1 hnotOld hnotReflect
  have hmask:=rootGeometryOfActualNativeContinuation_mask C s chain (g.datum.τ chi) sourceHeight budget b omega xi reserve mesh g
    hb1 hcard hs hlower hscale hwindow secondResidual L alloc liveRow hne Rdel hRdel hproper hcover hdelmesh
    (by simp only [omega,mul_one]) hR2 hP hfinite hgrid hcontinue.1 hnotOld hnotReflect
  have hu : 0<step.u:=lt_of_lt_of_le (by norm_num) hcontinue.1
  have hwide : st.width ≤ step.u:=hwidth
  have hhistory : Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
      modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
        (((0:Fin 4).val:ℝ)+1)/1000000000000000 :=by
    change Real.logb C.globalBase ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ _
    have hh:=hmask.1
    change Real.logb C.globalBase ((chain.R₂*chain.E₂).absNorm:ℝ) ≤
      modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
        1/1000000000000000 at hh
    simpa only [Fin.val_zero,Nat.cast_zero,zero_add,one_div] using hh
  let child:=nodeOfNativeContinuation C 0 C.globalBase 1 step.u Bmask hu (by rw [Real.rpow_one]) st hwide
    hmask.2 (chain.indices L alloc\Rdel) p
    (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 0)
    (rawDaughterScale (chain.final (g.datum.τ chi) sourceHeight) secondResidual L alloc 1)
    (raw_daughter_scale_pos _ _ _ _ 0) (raw_daughter_scale_pos _ _ _ _ 1)
    Next hcap rfl sourceHeight height hheight (fun i=>hfreq i.val) geom hhistory
  have hrowscale : child.unit*child.state.rowWidth=st.rowWidth :=by
    change (1*step.u)*(nativeContinuationState st step.u hu hwide hmask.2).rowWidth=_
    simpa only [one_mul] using native_continuation_global_row_scale st 1 step.u hu hwide hmask.2
  refine ⟨child,by change 1*step.u=step.u;ring,geom.unit_le_one,by rfl,?_,hrowscale,?_⟩
  · change Next.mult=_
    exact hmult
  · rw [hrowscale]
    exact hrelative
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_selected_source_child
