/- Definitional coordinates of the SAME actual native child callback. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeActualChild

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonProfile
open CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open Cycle63Moment.LowBranch Cycle153RegionalLow Cycle153ContinuationUnit
open Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

theorem actual_inner_native_child_package_coordinates (N : ReachableNode C j) (hj : j.val<3)
    (s : Input N.slots) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ n)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hX₁ : s.X₁=N.X1) (hX₂ : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset N.slots) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=N.state.puncture*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hcontinue : let r := nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
      Cycle153RegionalLow.nativeMainContinuation N.state r.u (ch.indices L alloc) Rdel
        (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (ch.final χ t) second L alloc 0)
        (rawDaughterScale (ch.final χ t) second L alloc 1))
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    let r:=nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
    let package:=actual_inner_native_child_package N hj s ch χ t n b Mrow omega xi reserve mesh g
      hb hcard hs hlower hX₁ hX₂ hscale second L alloc row hne Rdel hRdel hproper hcover hdelmesh
      homega hR₂ hPuncture hfinite hcontinue hgrid
    package.val.coordinates=extendCoordinates N.coordinates (nextInner j hj) r.V r.Red r.ell :=by
  rfl

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_native_child_package_coordinates
