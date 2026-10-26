/- Actual outer LOW source to the first reachable regional geometry. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootGeometry
import Candidate.Research.RecursiveAffine.NativeRootMask
import Candidate.Research.RecursiveAffine.NativeActualChild
import Candidate.Research.RecursiveAffine.NativeCommonMap
import Candidate.Research.RecursiveAffine.WeightedAttainer
import Candidate.Research.RecursiveAffine.NativeRootStepRebase
import Candidate.Research.RecursiveAffine.PhysicalChildContinuation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentEnergyState
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle63Moment.LowBranch Cycle153RootStep Cycle153Geometry Cycle153RegionalLow
open Cycle153ContinuationUnit
open Cycle153SourceReturn Cycle153RegionalLow CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearNormalization

noncomputable local instance rootCommonCallbacksLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- The same genuine first geometry retains the rootR=1 puncture receipt and yields mask20. -/
def actual_root_native_child_package
    (C : SourceContext (α:=α) M H)
    (s : Input α) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (bs omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi bs n)
    (hb : 1   ≤   bs) (hcard : Fintype.card α   ≤   n)
    (hs : s.upper   ≤   bs) (hlower : 1   ≤   s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion C.originalWeight   ≤   ∑i∈Rdel,C.originalWeight i)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i)   ≤   rootDetectorDeletion C.originalWeight+mesh)
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=(1:Ideal O)*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+
      (2*(n:ℝ)*Real.logb C.globalBase bs+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂))   ≤   1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)   ≤   positionMargin)
    (Bmask : ℝ)(st : NaturalState C.globalBase Bmask 2)
    (hcontinue :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve C.originalWeight g second L alloc Rdel
      nativeMainContinuation st r.u (ch.indices L alloc) Rdel C.originalWeight
        (rawDaughterScale (ch.final χ t) second L alloc 0)
        (rawDaughterScale (ch.final χ t) second L alloc 1)) :
    let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve C.originalWeight g second L alloc Rdel
    {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 r.u (ch.indices L alloc\Rdel)
      (rawDaughterScale (ch.final χ t) second L alloc 0)
      (rawDaughterScale (ch.final χ t) second L alloc 1) //
      Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          1/1000000000000000 ∧
      ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ (C.globalBase^r.u)^(20:ℝ)} :=by
  intro r
  have hdiff : @sdiff (Finset α) (@Finset.instSDiff α
      (Cycle153RegionalLow.strictCurrentDecidableEq (Current:=α))) (ch.indices L alloc) Rdel=
      ch.indices L alloc\Rdel:=native_sdiff_decEq _ _ (ch.indices L alloc) Rdel
  have hm:=hcontinue
  simp only[nativeMainContinuation,hdiff] at hm
  have hnotOld : r.u < length C.globalBase
      (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
      6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc\Rdel),C.originalWeight i) :=by
    simpa only[Finset.sum_coe_sort] using hm.2.2.1
  have hnotReflect :
      ¬(length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
        length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc\Rdel),C.originalWeight i)  ≤  r.u+19/5000 ∧
      (max 0 (r.u-length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+1/10000)+
        length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc\Rdel),C.originalWeight i)+19/5000  ≤  r.u ∨
       max 0 (r.u-length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)+1/10000)+
        length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc\Rdel),C.originalWeight i)+19/5000  ≤  r.u)) :=by
    simpa only[Finset.sum_coe_sort] using hm.2.2.2
  let geom:=rootGeometryOfActualNativeContinuation C s ch χ t n bs omega xi reserve mesh g
    hb hcard hs hlower hscale hwindow second L alloc row hne Rdel hRdel hm.2.1 hcover hdelmesh
    homega hR₂ hPuncture hfinite hgrid hm.1 hnotOld hnotReflect
  refine ⟨geom,?_⟩
  exact rootGeometryOfActualNativeContinuation_mask C s ch χ t n bs omega xi reserve mesh g
    hb hcard hs hlower hscale hwindow second L alloc row hne Rdel hRdel hm.2.1 hcover hdelmesh
    homega hR₂ hPuncture hfinite hgrid hm.1 hnotOld hnotReflect

/-- Literal common-source callback used by the root native Column producer.
The chosen common allocation is installed before constructing geometry,
history and mask; its residual allocation and nonzero row stay attached. -/
def actualCanonicalRootCommonChild
    (C : SourceContext (α:=α) M H)
    (s : Input α)(ch : Chain s)(χ : Character)(t : ℝ)
    (n : ℕ)(bs omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi bs n)
    (hb : 1 ≤ bs)(hcard : Fintype.card α ≤ n)(hs : s.upper ≤ bs)(hlower : 1 ≤ s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=(1:Ideal O)*ch.C₁)(hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+
      (2*(n:ℝ)*Real.logb C.globalBase bs+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (Ds : Finset (Ideal O))
    (daughter : PhysicalDaughter (withHeight ch.first χ t) ch.E₂ ch.R₂ Ds)
    (hn : commonScalar (withHeight ch.first χ t) ch.E₂ ch.R₂ daughter.1≠0)
    (Bmask : ℝ)(st : NaturalState C.globalBase Bmask 2)
    (row : O)
    (hne : Cycle63.Physical.sourcePositiveRow
      (commonData (withHeight ch.first χ t) ch.E₂ ch.R₂ daughter.1).toSource
      daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 row≠0)
    (Rdel : Finset α) :
    let chosenChain:=commonContinuationChain s ch χ t daughter.1
    let chosenGeometry:=commonContinuationGeometry g χ t daughter.1 hn
    ∀(hRdel : Rdel⊆chosenChain.indices daughter.2.1.1 daughter.2.2.1.1)
      (hcover : Rdel=chosenChain.indices daughter.2.1.1 daughter.2.2.1.1 ∨
        rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)
      (hdelmesh : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh),
    let r:=nativeRootStepValues s chosenChain χ t C.globalBase n bs 1 omega xi reserve C.originalWeight
      chosenGeometry daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 Rdel
    ∀(hc : nativeMainContinuation st r.u
      (chosenChain.indices daughter.2.1.1 daughter.2.2.1.1) Rdel C.originalWeight
      (rawDaughterScale (chosenChain.final χ t) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
      (rawDaughterScale (chosenChain.final χ t) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1)),
    {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 r.u
        (chosenChain.indices daughter.2.1.1 daughter.2.2.1.1\Rdel)
        (rawDaughterScale (chosenChain.final χ t) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
        (rawDaughterScale (chosenChain.final χ t) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1) //
      Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          1/1000000000000000 ∧
      ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ (C.globalBase^r.u)^(20:ℝ)} :=by
  intro chosenChain chosenGeometry hRdel hcover hdelmesh r hc
  exact actual_root_native_child_package C s chosenChain χ t n bs omega xi reserve mesh chosenGeometry
    hb hcard hs hlower hscale hwindow daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 row hne Rdel
    hRdel hcover hdelmesh homega hR₂ hPuncture hfinite hgrid Bmask st hc

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_child_package
#print axioms OAI.SevenEighths.Cycle153Reachable.actualCanonicalRootCommonChild
