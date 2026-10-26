/- Actual outer LOW source to the first reachable regional geometry. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCommonCallbacks
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

noncomputable local instance rootCoordinatesLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

theorem actual_root_native_child_package_coordinates
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
    (actual_root_native_child_package C s ch χ t n bs omega xi reserve mesh g
      hb hcard hs hlower hscale hwindow second L alloc row hne Rdel hRdel hcover hdelmesh
      homega hR₂ hPuncture hfinite hgrid Bmask st hcontinue).val.coordinates=
      rootCoordinates r.b r.rootSlack r.V r.Red r.ell :=by
  rfl

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_child_package_coordinates
