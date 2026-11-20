/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Both real first-arm packs hit the inherited selected source puncture. -/
import Candidate.C092.transport.ActualRootFrameHitSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentCanonicalFirst
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Packet
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {ι:Type} [Fintype ι]
variable (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr ι)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(h:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "src"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d h

theorem left_side_hit (η:Character) :
    let s:=src
    ∀(cover:OriginalEnclosure s)(C D:Id)(hC:Supported C)(E:Finset (CommonIndex C D))
      (ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀(B:actualAllocations (tuplePools s) C)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover C B J
    (SidePack.left F).base=F.left ∧ (SidePack.left F).V=firstPacked C D hC E ∧
      (SidePack.left F).Cs=C ∧ (SidePack.left F).Cs∣child.R ∧ child.R=C ∧
      (SidePack.left F).V≠0 := by
  intro s cover C D hC E ξ₁ ξ₂ F B J child
  have hm:=selected_masks M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d h cover C B J
  refine ⟨rfl,rfl,rfl,?_,hm.2.1,(SidePack.left F).hV⟩
  change C∣child.R
  rw [hm.2.1]

#print axioms left_side_hit

theorem right_side_hit (η:Character) :
    let s:=src
    ∀(cover:OriginalEnclosure s)(C D:Id)(hC:Supported C)(E:Finset (CommonIndex C D))
      (ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀(B:actualAllocations (tuplePools s) D)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover D B J
    (SidePack.right F).base=F.right ∧ (SidePack.right F).V=firstPackedRight C D hC E ∧
      (SidePack.right F).Cs=D ∧ (SidePack.right F).Cs∣child.R ∧ child.R=D ∧
      (SidePack.right F).V≠0 := by
  intro s cover C D hC E ξ₁ ξ₂ F B J child
  have hm:=selected_masks M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d h cover D B J
  refine ⟨rfl,rfl,rfl,?_,hm.2.1,(SidePack.right F).hV⟩
  change D∣child.R
  rw [hm.2.1]

#print axioms right_side_hit

end
end QRH.Cycle092.ActualRootFrameHit
