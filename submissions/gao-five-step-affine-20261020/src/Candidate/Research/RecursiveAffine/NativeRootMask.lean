/- Actual outer LOW source to the first reachable regional geometry. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootGeometry
import Candidate.Research.RecursiveAffine.NativeRootStepRebase
import Candidate.Research.RecursiveAffine.PhysicalChildContinuation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle63Moment.LowBranch Cycle153RootStep Cycle153Geometry Cycle153RegionalLow
open Cycle153ContinuationUnit

noncomputable local instance rootMaskLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- The same genuine first geometry retains the rootR=1 puncture receipt and yields mask20. -/
theorem rootGeometryOfActualNativeContinuation_mask
    (C : SourceContext (α:=α) M H)
    (s : Input α) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (bs omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi bs n)
    (hb : 1  ≤  bs) (hcard : Fintype.card α  ≤  n)
    (hs : s.upper  ≤  bs) (hlower : 1  ≤  s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion C.originalWeight  ≤  ∑i∈Rdel,C.originalWeight i)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i)  ≤  rootDetectorDeletion C.originalWeight+mesh)
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=(1:Ideal O)*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+
      (2*(n:ℝ)*Real.logb C.globalBase bs+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂))  ≤  1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)  ≤  positionMargin)
    (hwide :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      (397/1000:ℝ)  ≤  r.u)
    (hnotOld :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      r.u < length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
        length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc \ Rdel),C.originalWeight i))
    (hnotReflect :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      let x1:=length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)
      let x2:=length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)
      let z:=∑i : ↥(ch.indices L alloc \ Rdel),C.originalWeight i
      ¬(x1+x2+6*Cycle63.Optimization.slotPrice*z  ≤  r.u+19/5000 ∧
        (max 0 (r.u-x2+1/10000)+x1+6*Cycle63.Optimization.slotPrice*z+19/5000  ≤  r.u ∨
         max 0 (r.u-x1+1/10000)+x2+6*Cycle63.Optimization.slotPrice*z+19/5000  ≤  r.u))) :
    let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
      C.originalWeight g second L alloc Rdel
    let geom:=rootGeometryOfActualNativeContinuation C s ch χ t n bs omega xi reserve mesh g hb hcard hs hlower hscale hwindow
      second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR₂ hPuncture
      hfinite hgrid hwide hnotOld hnotReflect
    (Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
      modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
        1/1000000000000000) ∧
    ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ (C.globalBase^r.u)^(20:ℝ) := by
  intro r geom
  have hcoords : geom.coordinates=rootCoordinates r.b r.rootSlack r.V r.Red r.ell:=rfl
  have facts:=actual_outer_native_root_step s ch χ t C.globalBase C.globalBase_gt_one n bs 1
    omega xi reserve mesh C.originalWeight g hb hcard hs hlower C.originalWeight_nonneg hscale
    hwindow second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR₂ hPuncture hfinite
  rcases facts with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hcredit,hpad,_⟩
  have hlog : Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
      modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
        1/1000000000000000 := by
    rw [hcoords]
    exact rootCoordinates_puncture_history hcredit hpad
  refine ⟨hlog,?_⟩
  apply actual_child_mask_of_history C 0 geom.coordinates r.u
    (by simpa only [one_mul] using geom.unit_eq) (ch.R₂*ch.E₂) hPuncture geom.prefixRows
  simpa only [Fin.val_zero,Nat.cast_zero,zero_add] using hlog

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.rootGeometryOfActualNativeContinuation_mask
