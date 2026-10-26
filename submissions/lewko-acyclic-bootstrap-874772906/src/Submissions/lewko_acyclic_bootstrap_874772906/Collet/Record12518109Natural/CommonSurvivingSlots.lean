/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses Gao PR63's exact common-stage supply and original-slot partition,
transported to the pinned OpenAI/math and Cycle61 source interfaces. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.OriginalSlotPartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.SmallSlotDiscard
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.SlotMaximumTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentWholeSlotDeletion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge CenteredMomentHeckeSlots CenteredMomentCommonMaskExpansion
open CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondHeightFamily
open CommonSupply MarkedPlain WeightedHigh
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Common slot deletion is reindexed exactly by a fixed original subset;
no extra marked width is inserted into the density estimate. -/
theorem two_common_source_maximum_eq_subset
    (s : Input ι) (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (χ₁ : Character) (t₁ : ℝ) (E R₂ : Ideal O)
    (pick : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools E)
    (τ : Character) (t : ℝ) (z : O) (F : NaturalRow τ z) (hR : R₂*E≠0) :
    sourceSlotMaximum (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) τ t) E R₂ pick) z =
      ∏k∈originalSlots (fun k : liveIndices pick.val=>k.val.val),
        max 1 (‖naturalSlot (excluded F.character (R₂*E)) (s.slots k)
          (heightCoefficient (s.coefficient k) t) (s.P k)‖^2) := by
  change (∏k : liveIndices pick.val,
    max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R₂*E)) 1 z
      (s.slots k.val.val) (s.coefficient k.val.val) t (s.P k.val.val)‖^2))=_
  rw [double_subtype_prod (liveIndices B₁.val) (liveIndices pick.val)
    (fun k : ι=>max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R₂*E)) 1 z
      (s.slots k) (s.coefficient k) t (s.P k)‖^2))]
  apply Finset.prod_congr rfl
  intro k hk
  rw [masked_natural_slot_eq F _ hR]

/-- Both actual frozen coefficients supply the original logarithmic width.
Support padding and the total tiny-width discard remain explicit. -/
theorem eventual_two_common_large_width (N : ℕ) (a ε wmin : ℝ)
    (ha : 0<a) (hε : 0<ε) (hmin : 0≤wmin) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀s : Input ι,Fintype.card ι≤N →a≤s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : ι→ℝ,(∀k,s.P k=Z^(w k)) →(∀k,0≤w k) →
    let slots:=originalSlots (fun k : liveIndices B₂.val=>k.val.val)
    let large:=largeSlots slots w wmin
    0≤∑k∈large,w k ∧ (∑k∈large,w k)≤∑k,w k ∧
      (∑k,w k)-ε-(N:ℝ)*wmin≤Real.logb Z (C₁.absNorm:ℝ)+
        Real.logb Z (C₂.absNorm:ℝ)+∑k∈large,w k := by
  filter_upwards [eventual_two_stage_supplied_width (ι:=ι) N a ε ha hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale hw slots large
  have hcommon := hZ.2 s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale
  rw [double_subtype_sum (liveIndices B₁.val) (liveIndices B₂.val)] at hcommon
  have hlarge := large_width_lower slots w wmin N ((Finset.card_le_univ _).trans hcard) hmin
  refine ⟨Finset.sum_nonneg (fun k _=>hw k),Finset.sum_le_univ_sum_of_nonneg hw,?_⟩
  linarith only [hcommon,hlarge]

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.two_common_source_maximum_eq_subset
#print axioms OAI.SevenEighths.Record12518109Natural.eventual_two_common_large_width
