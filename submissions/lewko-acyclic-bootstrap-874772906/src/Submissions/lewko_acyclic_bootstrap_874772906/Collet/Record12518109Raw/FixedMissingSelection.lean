/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.FixedMissingFiber
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryHighFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open LocalMoment
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

/-- At one fixed missing radical, select a representative of the complete
nonnegative cost for every literal raw row. Units, sixth powers and the full
arithmetic label are retained. Only the small encoding multiplicity is paid;
this theorem does not sum missing radicals or assume a moment estimate. -/
theorem actual_fixed_missing_row_selection (B loss : ℝ)
    (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
      (Z : ℝ), 2 ≤ Z → ∀ (H : Ideal O), H ≠ 0 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀ l ∈ labels, ((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((Ideal.span {(nonzeroJointSourceRow l).val} * H).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, ps l.val.1.1.1 = ps l.val.1.1.2 ∧
        ps l.val.2.1.1 = ps l.val.2.1.2) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, firstSourceMissing left l.val.1 = H) →
      ∀ cost : labels → ℝ, (∀ l, 0 ≤ cost l) →
      let row := fun l : labels => nonzeroJointSourceRow l.val
      ∃ pick : (w : Finset.univ.image row) → labels,
        (∀ w, row (pick w) = w.val) ∧
        Function.Injective (fun w => row (pick w)) ∧
        (∑ l : labels, cost l) ≤ C * Z^loss *
          (∑ w : Finset.univ.image row, cost (pick w)) := by
  obtain ⟨C, hC, hcount⟩ := actual_joint_source_fixed_missing_count B loss hB hloss
  refine ⟨C, hC, ?_⟩
  intro left u₀ unit Z hZ H hH labels hrow hsupport hnonzero heq hnorm hmissing cost hc row
  have hW : 0 ≤ C * Z^loss := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  apply high_family_max_selection row cost (C * Z^loss) hW hc
  intro w
  let fiber := Finset.univ.filter (fun l : labels => row l = w)
  by_cases hempty : fiber = ∅
  · change (fiber.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact hW
  have hf : fiber.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨l₀, hl₀⟩ := hf
  have he₀ : row l₀ = w := (Finset.mem_filter.mp hl₀).2
  have hnrow : ((Ideal.span {w.val}).absNorm : ℝ) ≤ Z^B := by
    rw [← he₀]
    exact hrow l₀.val l₀.property
  have hnsupport : ((Ideal.span {w.val} * H).absNorm : ℝ) ≤ Z^B := by
    rw [← he₀]
    exact hsupport l₀.val l₀.property
  let forget := fun l : labels => l.val.val
  have hinj : Function.Injective forget := by
    intro l k h
    exact Subtype.ext (Subtype.ext h)
  have hb := hcount left u₀ unit Z hZ w.val w.property hnrow H hH hnsupport
    (fiber.image forget)
    (by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
      exact congrArg Subtype.val (Finset.mem_filter.mp hk).2)
    (by
      intro l hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      exact hnonzero k.val k.property)
    (by
      intro l hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      exact heq k.val k.property)
    (by
      intro l hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      exact hnorm k.val k.property)
    (by
      intro l hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      exact hmissing k.val k.property)
  rwa [Finset.card_image_of_injective _ hinj] at hb

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_missing_row_selection
