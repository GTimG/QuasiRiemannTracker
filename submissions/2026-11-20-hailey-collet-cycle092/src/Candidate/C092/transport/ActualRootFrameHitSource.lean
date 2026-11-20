/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Literal projectors on the genuine collision/inverse divided source. -/
import Candidate.C092.transport.ActualStageFrameBudgetProducer
import Candidate.C092.transport.OrderedPairActualRestoredGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) actualHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type} [Fintype ι]
variable (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr ι)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(h:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "src"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d h

theorem divided_masks : (src).H=∅ ∧ (src).R=1 ∧ (src).Fhole=1 ∧ (src).d=(1,1) := ⟨rfl,rfl,rfl,rfl⟩

theorem selected_masks :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    (child).H=∅ ∧ (child).R=G ∧ (child).Fhole=1 ∧ (child).d=(1,1) := by
  intro s cover G B J child
  refine ⟨rfl,?_,rfl,rfl⟩
  change (1:Id)*G=G
  exact one_mul G

theorem selected_profiles :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    (child).W₁=r.p.profile 0 ∧ (child).W₂=r.p.profile 1 ∧ (child).t₁=t₁ ∧ (child).t₂=t₂ := by
  intro s cover G B J child
  exact   ⟨rfl,rfl,rfl,rfl⟩

theorem selected_controls (S:Finset (ℕ×ℕ)) :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    sourceControl S (child).W₁*sourceControl S (child).W₂=r.p.control S := by
  intro s cover G B J child
  rfl

theorem selected_heights :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    2+‖(child).t₁‖+‖(child).t₂‖=2+‖t₁‖+‖t₂‖ := by
  intro s cover G B J child
  rfl

theorem selected_lengths :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    (child).X₁=(X₁/(d.1.absNorm:ℝ))/(B.val (Sum.inr 0)).absNorm ∧
    (child).X₂=(X₂/(d.2.absNorm:ℝ))/(B.val (Sum.inr 1)).absNorm ∧
    (child).Y₁=(Y₁/(d.1.absNorm:ℝ))/(B.val (Sum.inr 0)).absNorm ∧
    (child).Y₂=(Y₂/(d.2.absNorm:ℝ))/(B.val (Sum.inr 1)).absNorm := by
  intro s cover G B J child
  change _/(((1:Id)*B.val (Sum.inr 0)).absNorm:ℝ)=_ ∧
    _/(((1:Id)*B.val (Sum.inr 1)).absNorm:ℝ)=_ ∧
    _/(((1:Id)*B.val (Sum.inr 0)).absNorm:ℝ)=_ ∧
    _/(((1:Id)*B.val (Sum.inr 1)).absNorm:ℝ)=_
  simp only [one_mul]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem selected_floor :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    (child).L=
    min (min (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ)))
      (min (Y₁/(d.1.absNorm:ℝ)) (Y₂/(d.2.absNorm:ℝ)))/
      (((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm) := by
  intro s cover G B J child
  change _/((((1:Id)*B.val (Sum.inr 0)).absNorm:ℝ)*((1:Id)*B.val (Sum.inr 1)).absNorm)=_
  simp only [one_mul]
  rfl

theorem selected_prime_scale_cap :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    ∀i,(child).P i ≤ r.Z := by
  intro s cover G B J child
  intro i
  change r.Z^(r.w (originalSlot s (by norm_num) cover G B J i)) ≤ r.Z
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le r.hZ.le
    ((r.hwcap _).trans (by norm_num : (1/6:ℝ) ≤ 1))

theorem selected_mark_bound :
    let s:=src
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    ∀i,(child).M i=RestoredRootSource.slotBound r.W r.hW r.hWs := by
  intro s cover G B J child
  exact fun _=>rfl

#print axioms selected_masks
#print axioms selected_controls
#print axioms selected_lengths
#print axioms selected_floor
#print axioms selected_prime_scale_cap
end
end QRH.Cycle092.ActualRootFrameHit
