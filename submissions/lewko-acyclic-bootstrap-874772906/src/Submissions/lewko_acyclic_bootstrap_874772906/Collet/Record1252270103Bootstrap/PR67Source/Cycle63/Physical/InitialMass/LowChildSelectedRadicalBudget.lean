import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowAggregate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildRadicalBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The selected first-pair fibers of a LOW child pay second-label contributions that are pointwise bounded by the
reciprocal common-radical norm. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle63Moment Cycle63FinalCapacity

/-- The label-indexed analogue of `actual_low_pointwise_label_budget`: the contributions of the second labels of all
selected first pairs sum to at most `K Z^(p + exponent + errbar + ε)` over the seed norm. -/
theorem actual_selected_low_supported_pointwise_budget (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {Label : Type*} [Fintype Label]
    (second : Bool) (Z T p exponent errbar : ℝ),
    2 ≤ Z → 1 ≤ T → p ≤ B → ∀ seed₀ : Ideal O, Squarefree seed₀ → seed₀ ≠ 0 →
    ∀ (first : Label → FirstSourceLabel) (seed : Label → Ideal O),
    Function.Injective (fun j => (first j, seed j)) →
    (∀ j, Supported (first j).1.1 ∧ Supported (first j).1.2) →
    (∀ j, primeSupport (first j).1.1 = primeSupport (first j).1.2) →
    (∀ j, seed₀ ∣ (first j).1.1 ∧ seed₀ ∣ (first j).1.2) →
    (∀ j, ((first j).1.1.absNorm : ℝ) ≤ Z ^ B ∧ ((first j).1.2.absNorm : ℝ) ≤ Z ^ B) →
    (∀ j, ((commonRadical (first j).1.1 (first j).1.2).absNorm : ℝ) ≤ Z ^ p) →
    ∀ (geom : FirstSourceLabel → ℝ) (err : FirstSourceLabel → FirstSourceLabel → ℝ),
    (∀ j, geom (first j) ≤ exponent) →
    (∀ j, Squarefree (seed j)) →
    (∀ j, T ≤ ((seed j).absNorm : ℝ) ∧ ((seed j).absNorm : ℝ) < 2 * T) →
    ∀ children : Label → Finset FirstSourceLabel,
    (∀ j, ∀ v ∈ children j, Supported v.1.1 ∧ Supported v.1.2) →
    (∀ j, ∀ v ∈ children j, primeSupport v.1.1 = primeSupport v.1.2) →
    (∀ j, ∀ v ∈ children j, seed j ∣ v.1.1 ∧ seed j ∣ v.1.2) →
    (∀ j, ∀ v ∈ children j, (v.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (v.1.2.absNorm : ℝ) ≤ Z ^ B) →
    (∀ j, ∀ v ∈ children j, Z ^ (err (first j) v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ) ≤
      Z ^ errbar / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) →
    (∑ j, ∑ v ∈ children j, Z ^ (geom (first j) + err (first j) v) /
      ((if second then v.1.2 else v.1.1).absNorm : ℝ)) ≤
      K₀ * Z ^ (p + exponent + errbar + ε) / (seed₀.absNorm : ℝ) := by
  obtain ⟨K₀, hK₀, hbudget⟩ := actual_low_pointwise_label_budget B ε hB hε
  refine ⟨K₀, hK₀, ?_⟩
  intro Label _ second Z T p exponent errbar hZ hT hp seed₀ hs hs0 first seed hinj
    hsup heq hseed hnorm hrad geom err hgeom hsq hdyad children hsup₂ heq₂ hseed₂ hnorm₂ hpoint
  rw [selected_low_supported_sum first seed hinj children
    (fun l v => Z ^ (geom l + err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ))]
  apply hbudget second Z T p exponent errbar hZ hT hp seed₀ hs hs0 (selectedLowFirstLabels first)
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact hsup j
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact heq j
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact hseed j
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact hnorm j
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact hrad j
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact hgeom j
  · intro l _ D hD
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    exact hsq j
  · intro l _ D hD
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    exact hdyad j
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren, dite_eq_left ⟨hl, hD⟩] at hv
    exact hsup₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren, dite_eq_left ⟨hl, hD⟩] at hv
    exact heq₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren, dite_eq_left ⟨hl, hD⟩] at hv
    have hf := (selected_low_pair_inverse_fields first seed hinj ⟨⟨l, hl⟩, ⟨D, hD⟩⟩).2
    simpa only [hf] using hseed₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren, dite_eq_left ⟨hl, hD⟩] at hv
    exact hnorm₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren, dite_eq_left ⟨hl, hD⟩] at hv
    have hf := (selected_low_pair_inverse_fields first seed hinj ⟨⟨l, hl⟩, ⟨D, hD⟩⟩).1
    simpa only [hf] using hpoint _ v hv

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
