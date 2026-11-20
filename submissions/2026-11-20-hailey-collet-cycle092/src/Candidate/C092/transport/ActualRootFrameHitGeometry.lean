/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Transport the proved physical first-hit geometry to its actual finite source. -/
import Candidate.C092.transport.ActualRootFrameHitSupport
import Candidate.C092.transport.RestoredFirstHitGeometry
import Candidate.C092.transport.RestoredFrameRectangles
import Candidate.C092.transport.ActualColoredCutoff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CenteredMomentEnergyBands
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.NativeStrip QRH.Cycle090
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) geometryHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type} [Fintype ι]

/-- Exactly the genuine inverse-restored volume/floor ledger after the
    native finite reindex. The underlying geometric argument is unchanged. -/
theorem selected_restored_ledger (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(r:RestoredRootSource.Data M Hr ι)
    (X₁ X₂ Y₁ Y₂ t₁ t₂ n y l:ℝ)(d:IdealPair)(hd₁:d.1≠0)(hd₂:d.2≠0)
    (g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
    (hx₁:length r.Z X₁ ≤ n)(hx₂:length r.Z X₂ ≤ y)
    (hy0:sourceY0 ≤ y)(hy1:y ≤ sourceY)(hn:n ≤ sourceRatio*y)
    (hws:(∑i,r.w i) ≤ l)(hl:l ≤ sourceWidth n y)
    (hshort:∀X∈({X₁,X₂,Y₁,Y₂}:Finset ℝ),r.Z^(115/1000:ℝ) ≤ X) :
    let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
    ∀(cover:OriginalEnclosure s)(G:Id)(hG:G≠0)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let u':=∑j∈J,r.w j.val
    let child:=originalSelectedSource s (by norm_num) cover G B J
    let c:=Real.logb r.Z (((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ))
    Real.logb r.Z (sourceVolume child) ≤ 9179599/10000000-c-u'+Real.logb r.Z ((2:ℝ)^Fintype.card ι) ∧
    max 0 (115/1000-c) ≤ Real.logb r.Z (max 1 child.L) := by
  intro s cover G hG B J u' child c
  have hh:=FixedFramePacking.exact_restored_ledger M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ n y l d hd₁ hd₂
    g hx₁ hx₂ hy0 hy1 hn hws hl hshort cover G hG B J
  change Real.logb r.Z (sourceVolume (originalSelectedSource s (by norm_num) cover G B J)) ≤ _ ∧
    max 0 (115/1000-c) ≤ Real.logb r.Z (max 1 (originalSelectedSource s (by norm_num) cover G B J).L)
  simpa only [selected_volume_eq,selected_floor_eq] using hh

/-- The actual reference .115/.72092 rectangle is retained. No reference
    coordinate is put into the original X-arm Box. -/
theorem selected_rectangles (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(r:RestoredRootSource.Data M Hr ι)
    (X₁ X₂ t₁ t₂ n y:ℝ)(d:IdealPair)(hd₁:d.1≠0)(hd₂:d.2≠0)
    (g:DividedLengths r.Z X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) d)
    (hL:length r.Z X₁ ≤ n)(hS:length r.Z X₂ ≤ y)(hy:y ≤ sourceY)(hn:n ≤ sourceRatio*y) :
    let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
    let child:=originalSelectedSource s (by norm_num) cover G B J
    child.X₁ ≤ r.Z^n ∧ child.X₂ ≤ r.Z^y ∧ child.Y₁ ≤ r.Z^(115/1000:ℝ) ∧ child.Y₂ ≤ r.Z^(72092/100000:ℝ) := by
  intro s cover G B J child
  exact FixedFramePacking.actual_rectangles M Hr hHr r X₁ X₂ t₁ t₂ n y d hd₁ hd₂ g hL hS hy hn cover G B J

/-- One scalar threshold before all actual sources, selected subsets and
    positive root fees pays the precise native second-cutoff debit. -/
theorem actual_cutoff_fee (N:ℕ)(ξ mesh:ℝ)(hsep:ξ/2 < mesh) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N →
    ∀(cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)),
      32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest J))^2*Z^(ξ/2) ≤ Z^mesh := by
  filter_upwards [FixedFramePacking.frequency_fee N (9/4) ξ mesh hsep] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hN cover G B J
  have hcard : Fintype.card (Rest J) ≤ N := by
    apply (Fintype.card_le_of_injective (fun j : Rest J => j.val.val) ?_).trans hN
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  exact hz.2 _ hcard

#print axioms selected_restored_ledger
#print axioms selected_rectangles
#print axioms actual_cutoff_fee
end
end QRH.Cycle092.ActualRootFrameHit
