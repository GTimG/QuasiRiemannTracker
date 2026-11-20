/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0. -/
import Candidate.C092.transport.ColoredSelectionAverageRaw
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteAssemblyAvgBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredSelectionAverage
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- A valid image multiplicity can be clipped by the full assignment count.
    Main terms retain its sharper subpower cap; diagonal terms may use the count. -/
def clippedMultiplicity (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (B : actualAllocations (tuplePools s) G) : ℝ :=
  min (M B) ((selY (allocatedLiveSource s hb cover G B) (J B)).card:ℝ)

theorem clippedMultiplicity_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (B : actualAllocations (tuplePools s) G) :
    clippedMultiplicity s hb cover G J M B ≤ M B := min_le_left _ _

theorem clippedMultiplicity_le_card (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (B : actualAllocations (tuplePools s) G) :
    clippedMultiplicity s hb cover G J M B ≤
      ((selY (allocatedLiveSource s hb cover G B) (J B)).card:ℝ) := min_le_right _ _

theorem multBound_clipped (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (K : ℝ) (W M : actualAllocations (tuplePools s) G→ℝ)
    (hM : MultBound s hb cover G J K W M) :
    MultBound s hb cover G J K W (clippedMultiplicity s hb cover G J M) := by
  intro B
  refine ⟨le_min (hM B).1 (Nat.cast_nonneg _),?_⟩
  intro z hz hzn
  apply le_min ((hM B).2 z hz hzn)
  exact_mod_cast Finset.card_filter_le (selY (allocatedLiveSource s hb cover G B) (J B)) _

/-- The common radius is the native full selected-slot width, not an
    independent arbitrary scale. -/
theorem widthBound_actual {ι : Type} [Fintype ι] (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val)) :
    WidthBound s hb cover G J (fun B=>RawSides.selectionScaleQ s hb cover G B (J B)) := by
  have he : (fun B : actualAllocations (tuplePools s) G =>
      slotWidth (allocatedLiveSource s hb cover G B) (J B)) =
      (fun B => RawSides.selectionScaleQ s hb cover G B (J B)) := by
    funext B
    exact ColoredGaussSelection.scale_eq_actual s hb cover G B (J B)
  exact he ▸ widthBound_slot s hb cover G J

#print axioms multBound_clipped
#print axioms widthBound_actual
end
end QRH.Cycle092.ColoredSelectionAverage
