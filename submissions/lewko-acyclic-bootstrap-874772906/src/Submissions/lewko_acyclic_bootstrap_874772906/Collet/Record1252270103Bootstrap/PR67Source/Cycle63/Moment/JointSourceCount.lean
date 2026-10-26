import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.SecondSourceEncoding
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.SecondCommonRadical
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

theorem joint_source_second_generator_dvd (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (label : JointSourceLabel) :
    commonFrequencyGenerator label.2.1.1 label.2.1.2 ∣ jointSourceRow left u₀ unit label := by
  refine ⟨(u₀*unit label.1)*
    primeSubsetGenerator (fun P : CommonIndex label.1.1.1 label.1.1.2 => P.val) label.1.2.val*
    firstSourceNumerator left label.1*
    nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1*label.2.2.val.2,?_⟩
  dsimp only [jointSourceRow,effectiveRow]
  ring

theorem joint_source_fixed_row_pair_injOn (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (w : O) (hw : w ≠ 0)
    (labels : Set JointSourceLabel)
    (hrow : ∀ label ∈ labels, jointSourceRow left u₀ unit label = w)
    (hsupported : ∀ label ∈ labels, Supported label.2.1.1) :
    Set.InjOn (fun label : JointSourceLabel => (label.1,label.2.1)) labels := by
  intro a ha b hb hab
  have hf : a.1 = b.1 := congrArg
    (fun p : FirstSourceLabel × (Ideal O × Ideal O) => p.1) hab
  have hs : a.2.1 = b.2.1 := congrArg
    (fun p : FirstSourceLabel × (Ideal O × Ideal O) => p.2) hab
  apply joint_source_key_injOn left u₀ unit labels
    (fun label hl => hrow label hl ▸ hw) hsupported ha hb
  change (jointSourceRow left u₀ unit a,(firstSourceKey left a.1,a.2.1)) =
    (jointSourceRow left u₀ unit b,(firstSourceKey left b.1,b.2.1))
  exact Prod.ext ((hrow a ha).trans (hrow b hb).symm)
    (Prod.ext (congrArg (firstSourceKey left) hf) hs)

/-- This counts the actual common-pair, projector, partition and residual-frequency
labels after the residual second projector has been contracted analytically. -/
theorem actual_joint_source_row_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ w : O, w ≠ 0 → (Ideal.absNorm (Ideal.span {w}):ℝ) ≤ Z^B →
      ∀ m : ℝ, ∀ labels : Finset JointSourceLabel,
      (∀ label ∈ labels, jointSourceRow left u₀ unit label = w) →
      (∀ label ∈ labels, Supported label.1.1.1 ∧ label.1.1.2 ≠ 0 ∧
        Supported label.2.1.1 ∧ label.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.1.1.1 = primeSupport label.1.1.2 ∧
        primeSupport label.2.1.1 = primeSupport label.2.1.2) →
      (∀ label ∈ labels, ((Ideal.span {w}*firstSourceMissing left label.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.1.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.1).absNorm:ℝ) ≤ Z^m) →
      (labels.card:ℝ) ≤ C*Z^(m+loss) := by
  obtain ⟨C₁,hC₁,hfirst⟩ := actual_first_source_row_count B (loss/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hsecond⟩ := Cycle63.Physical.uniform_common_pair_count B (loss/2) hB (by positivity)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro left u₀ unit Z hZ w hw hwnorm m labels hrow hnonzero heq hsupportnorm hnorm hmissing
  have hf := hfirst left Z hZ w hw m (labels.image (fun label => label.1))
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact ⟨(hnonzero label hl).1,(hnonzero label hl).2.1⟩)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact (heq label hl).1)
    (by
      intro first hf
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨u₀*unit label.1,commonFrequencyGenerator label.2.1.1 label.2.1.2,
        nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1,
        label.2.2.val.2,(hrow label hl).symm⟩)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact hsupportnorm label hl)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact ⟨(hnorm label hl).1,(hnorm label hl).2.1⟩)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact hmissing label hl)
  have hs := hsecond Z hZ (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw) hwnorm
    (labels.image (fun label => label.2.1))
    (by intro second hs; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs; exact ⟨(hnonzero label hl).2.2.1.1,(hnonzero label hl).2.2.2⟩)
    (by intro second hs; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs; exact (heq label hl).2)
    (by
      intro second hs
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs
      apply Cycle63.Physical.common_support_in_row _ _ (hnonzero label hl).2.2.1
        (heq label hl).2 w hw
      rw [←hrow label hl]
      exact joint_source_second_generator_dvd left u₀ unit label)
    (by intro second hs; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs; exact (hnorm label hl).2.2)
  have hc : labels.card ≤ (labels.image (fun label => label.1)).card *
      (labels.image (fun label => label.2.1)).card := by
    rw [←Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun label : JointSourceLabel => (label.1,label.2.1))
    · intro label hl
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hl,Finset.mem_image_of_mem _ hl⟩
    · exact joint_source_fixed_row_pair_injOn left u₀ unit w hw labels hrow
        (fun label hl => (hnonzero label hl).2.2.1)
  calc
    _ ≤ ((labels.image (fun label => label.1)).card:ℝ)*
        ((labels.image (fun label => label.2.1)).card:ℝ) := by exact_mod_cast hc
    _ ≤ (C₁*Z^(m+loss/2))*(C₂*Z^(loss/2)) :=
      mul_le_mul hf hs (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      calc
        _ = (C₁*C₂)*(Z^(m+loss/2)*Z^(loss/2)) := by ring
        _ = _ := by
          rw [←Real.rpow_add (by linarith : 0 < Z)]
          congr 1
          ring_nf

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
