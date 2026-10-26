/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualFamilyRebase

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn

/-- A whole actual returned forest may be chosen within a factor two of
its source-wide supremum. Its terminal depths and all source metadata stay
together. The rough upper bound must be proved from the actual arithmetic
source; this lemma does not assume a sharp record price or prove that
rough bound. No cardinality of source configurations is charged. -/
theorem whole_source_forest_attainer
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} {Config : Type*} [Fintype Depth] [Nonempty Config]
    {junction : Depth → ℝ} {Base : Depth → Type}
    {base : (d : Depth) → Character → Base d → Character}
    {eta : Character} {Z B T : ℝ} {root : O}
    (F : Config → DepthReturnedFamily M H hH junction Base base eta Z B T root)
    (hZ : 0 ≤ Z)
    (hbounded : BddAbove (Set.range (fun c => (F c).value))) :
    ∃ chosen : Config, ∀ c : Config, (F c).value ≤ 2*(F chosen).value := by
  classical
  let values : Set ℝ := Set.range (fun c => (F c).value)
  have hne : values.Nonempty := Set.range_nonempty _
  by_cases hpos : ∃ c : Config, 0 < (F c).value
  · obtain ⟨c, hc⟩ := hpos
    have hspos : 0 < sSup values := hc.trans_le (le_csSup hbounded ⟨c,rfl⟩)
    obtain ⟨value, ⟨chosen, rfl⟩, hnear⟩ := exists_lt_of_lt_csSup hne
      (show sSup values/2 < sSup values by linarith)
    refine ⟨chosen, fun c => ?_⟩
    have hle := le_csSup hbounded (show (F c).value ∈ values from ⟨c,rfl⟩)
    linarith only [hnear,hle]
  · obtain ⟨chosen⟩ := ‹Nonempty Config›
    refine ⟨chosen, fun c => ?_⟩
    have hc : (F c).value ≤ 0 := le_of_not_gt (fun hc => hpos ⟨c,hc⟩)
    have hchosen := (F chosen).value_nonneg hZ
    linarith only [hc,hchosen]

/-- The same whole attaining forest is used for every source
configuration and every terminal depth. The factor two is a fixed source
constant, not a new exponent or a separately selected reduction. -/
theorem whole_source_forest_attainer_with_metadata
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} {Config : Type*} [Fintype Depth] [Nonempty Config]
    {junction : Depth → ℝ} {Base : Depth → Type}
    {base : (d : Depth) → Character → Base d → Character}
    {eta : Character} {Z B T : ℝ} {root : O}
    (Meta : Config → Type) (metadata : (c : Config) → Meta c)
    (F : Config → DepthReturnedFamily M H hH junction Base base eta Z B T root)
    (hZ : 0 ≤ Z)
    (hbounded : BddAbove (Set.range (fun c => (F c).value))) :
    ∃ chosen : Config, Nonempty (Meta chosen) ∧
      ∀ c : Config, (F c).value ≤ 2*(F chosen).value := by
  obtain ⟨chosen,hchosen⟩ := whole_source_forest_attainer F hZ hbounded
  exact ⟨chosen,⟨metadata chosen⟩,hchosen⟩

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.whole_source_forest_attainer
#print axioms OAI.SevenEighths.Cycle153RegionalLow.whole_source_forest_attainer_with_metadata
