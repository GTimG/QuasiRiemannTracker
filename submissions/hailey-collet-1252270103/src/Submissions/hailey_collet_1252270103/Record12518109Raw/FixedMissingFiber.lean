/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The counting arguments extract the fixed-radical fibers of Cycle61. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.JointSourceCount

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum
open Cycle61Moment
local notation "O" => HeckeFamily.O

/-- The first label fiber at a fixed literal row and a fixed missing radical.
Unlike `actual_first_source_row_count`, this has no linear radical payment:
that payment belongs to a subsequent sum over the distinct missing radicals. -/
theorem actual_first_source_fixed_missing_count
    (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ Z : ℝ, 2 ≤ Z →
      ∀ w : O, w ≠ 0 → ∀ H : Ideal O, H ≠ 0 →
      ((Ideal.span {w} * H).absNorm : ℝ) ≤ Z ^ B →
      ∀ labels : Finset FirstSourceLabel,
      (∀ label ∈ labels, Supported label.1.1 ∧ label.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.1.1 = primeSupport label.1.2) →
      (∀ label ∈ labels, ∃ u₀ G V h : O,
        w = effectiveRow u₀
          (primeSubsetGenerator (fun P : CommonIndex label.1.1 label.1.2 => P.val) label.2.val)
          (firstSourceNumerator left label) G V h) →
      (∀ label ∈ labels, (label.1.1.absNorm : ℝ) ≤ Z ^ B ∧
        (label.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ label ∈ labels, firstSourceMissing left label = H) →
      (labels.card : ℝ) ≤ C * Z ^ loss := by
  obtain ⟨C, hC, hpair⟩ := Cycle61.Physical.uniform_common_pair_count B loss hB hloss
  refine ⟨C, hC, ?_⟩
  intro left Z hZ w hw H hH hsupportnorm labels hnonzero heq hliteral hnorm hmissing
  have hinj : Set.InjOn (fun label : FirstSourceLabel => label.1)
      (↑labels : Set FirstSourceLabel) := by
    intro a ha b hb hab
    apply first_source_key_injective left
    exact Prod.ext hab ((hmissing a ha).trans (hmissing b hb).symm)
  have hb := hpair Z hZ (Ideal.span {w} * H)
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hH) hsupportnorm
    (labels.image (fun label => label.1))
    (by
      intro p hp
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨(hnonzero label hl).1.1, (hnonzero label hl).2⟩)
    (by
      intro p hp
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hp
      exact heq label hl)
    (by
      intro p hp
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hp
      have hs := first_source_literal_support left label (hnonzero label hl).1
        (heq label hl) w hw (hliteral label hl)
      rwa [hmissing label hl] at hs)
    (by
      intro p hp
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hp
      exact hnorm label hl)
  rwa [Finset.card_image_of_injOn hinj] at hb

/-- Both common-pair encodings at fixed literal row and fixed missing radical.
The original units, inactive projectors and residual frequency remain in
`JointSourceLabel` and `jointSourceRow`. No radical summation is performed. -/
theorem actual_joint_source_fixed_missing_count
    (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ w : O, w ≠ 0 →
      ((Ideal.span {w}).absNorm : ℝ) ≤ Z ^ B →
      ∀ H : Ideal O, H ≠ 0 → ((Ideal.span {w} * H).absNorm : ℝ) ≤ Z ^ B →
      ∀ labels : Finset JointSourceLabel,
      (∀ label ∈ labels, jointSourceRow left u₀ unit label = w) →
      (∀ label ∈ labels, Supported label.1.1.1 ∧ label.1.1.2 ≠ 0 ∧
        Supported label.2.1.1 ∧ label.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.1.1.1 = primeSupport label.1.1.2 ∧
        primeSupport label.2.1.1 = primeSupport label.2.1.2) →
      (∀ label ∈ labels, (label.1.1.1.absNorm : ℝ) ≤ Z ^ B ∧
        (label.1.1.2.absNorm : ℝ) ≤ Z ^ B ∧
        (label.2.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (label.2.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ label ∈ labels, firstSourceMissing left label.1 = H) →
      (labels.card : ℝ) ≤ C * Z ^ loss := by
  obtain ⟨C₁, hC₁, hfirst⟩ := actual_first_source_fixed_missing_count
    B (loss / 2) hB (by positivity)
  obtain ⟨C₂, hC₂, hsecond⟩ := Cycle61.Physical.uniform_common_pair_count
    B (loss / 2) hB (by positivity)
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro left u₀ unit Z hZ w hw hwnorm H hH hsupportnorm labels hrow hnonzero heq hnorm hmissing
  have hf := hfirst left Z hZ w hw H hH hsupportnorm
    (labels.image (fun label => label.1))
    (by
      intro first hf
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(hnonzero label hl).1, (hnonzero label hl).2.1⟩)
    (by
      intro first hf
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hf
      exact (heq label hl).1)
    (by
      intro first hf
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hf
      exact ⟨u₀ * unit label.1, commonFrequencyGenerator label.2.1.1 label.2.1.2,
        nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1,
        label.2.2.val.2, (hrow label hl).symm⟩)
    (by
      intro first hf
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(hnorm label hl).1, (hnorm label hl).2.1⟩)
    (by
      intro first hf
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hf
      exact hmissing label hl)
  have hs := hsecond Z hZ (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw)
    hwnorm (labels.image (fun label => label.2.1))
    (by
      intro second hs
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨(hnonzero label hl).2.2.1.1, (hnonzero label hl).2.2.2⟩)
    (by
      intro second hs
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hs
      exact (heq label hl).2)
    (by
      intro second hs
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hs
      apply Cycle61.Physical.common_support_in_row _ _ (hnonzero label hl).2.2.1
        (heq label hl).2 w hw
      rw [← hrow label hl]
      exact joint_source_second_generator_dvd left u₀ unit label)
    (by
      intro second hs
      obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hs
      exact (hnorm label hl).2.2)
  have hc : labels.card ≤ (labels.image (fun label => label.1)).card *
      (labels.image (fun label => label.2.1)).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun label : JointSourceLabel => (label.1, label.2.1))
    · intro label hl
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hl, Finset.mem_image_of_mem _ hl⟩
    · exact joint_source_fixed_row_pair_injOn left u₀ unit w hw labels hrow
        (fun label hl => (hnonzero label hl).2.2.1)
  calc
    _ ≤ ((labels.image (fun label => label.1)).card : ℝ) *
        ((labels.image (fun label => label.2.1)).card : ℝ) := by exact_mod_cast hc
    _ ≤ (C₁ * Z ^ (loss / 2)) * (C₂ * Z ^ (loss / 2)) :=
      mul_le_mul hf hs (Nat.cast_nonneg _) (by positivity)
    _ = (C₁ * C₂) * (Z ^ (loss / 2) * Z ^ (loss / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by linarith : 0 < Z), show loss / 2 + loss / 2 = loss by ring]

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.actual_first_source_fixed_missing_count
#print axioms OAI.SevenEighths.Record12518109Raw.actual_joint_source_fixed_missing_count
