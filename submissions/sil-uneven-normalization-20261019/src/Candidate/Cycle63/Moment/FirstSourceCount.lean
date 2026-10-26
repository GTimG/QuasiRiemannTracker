import Candidate.Cycle63.Moment.FirstSourceEncoding
import Candidate.Cycle63.Physical.JointRowFibres

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open ActualEisensteinCubic
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

def firstSourceMissing (left : Bool) (label : FirstSourceLabel) : Ideal O :=
  firstMissingRadical label.1.1 label.1.2 label.2.val left

def firstSourceNumerator (left : Bool) (label : FirstSourceLabel) : O :=
  if left then firstLeftUncancelled label.1.1 label.1.2
    else firstRightUncancelled label.1.1 label.1.2

theorem first_source_literal_support (left : Bool) (label : FirstSourceLabel)
    (hC : Supported label.1.1)
    (hCD : primeSupport label.1.1 = primeSupport label.1.2)
    (w : O) (hw : w ≠ 0)
    (hliteral : ∃ u₀ G V h : O,
      w = effectiveRow u₀
        (primeSubsetGenerator (fun P : CommonIndex label.1.1 label.1.2 => P.val) label.2.val)
        (firstSourceNumerator left label) G V h) :
    primeSupport label.1.1 ⊆ primeSupport (Ideal.span {w}*firstSourceMissing left label) := by
  obtain ⟨u₀,G,V,h,rfl⟩ := hliteral
  cases left
  · exact actual_first_right_support_visible _ _ hC hCD _ label.2.property u₀ G V h hw
  · exact actual_first_left_support_visible _ _ hC hCD _ label.2.property u₀ G V h hw

/-- Arbitrary first common valuations and the inactive projector are reconstructed
inside each literal signed row, with only its missing radical counted linearly. -/
theorem actual_first_source_row_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ Z : ℝ, 2 ≤ Z →
      ∀ w : O, w ≠ 0 → ∀ m : ℝ, ∀ labels : Finset FirstSourceLabel,
      (∀ label ∈ labels, Supported label.1.1 ∧ label.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.1.1 = primeSupport label.1.2) →
      (∀ label ∈ labels, ∃ u₀ G V h : O,
        w = effectiveRow u₀
          (primeSubsetGenerator (fun P : CommonIndex label.1.1 label.1.2 => P.val) label.2.val)
          (firstSourceNumerator left label) G V h) →
      (∀ label ∈ labels, ((Ideal.span {w}*firstSourceMissing left label).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label).absNorm:ℝ) ≤ Z^m) →
      (labels.card:ℝ) ≤ C*Z^(m+loss) := by
  obtain ⟨C,hC,hpair⟩ := Cycle63.Physical.uniform_common_pair_count B loss hB hloss
  refine ⟨128*C,by positivity,?_⟩
  intro left Z hZ w hw m labels hnonzero heq hliteral hsupportnorm hnorm hmissing
  let missing : FirstSourceLabel → Ideal O := firstSourceMissing left
  have hmissing0 (label : FirstSourceLabel) (hl : label ∈ labels) : missing label ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt (firstCommonSubsetNorm_pos _ _
      (hnonzero label hl).1 (firstMissingCommon _ _ label.2.val left)))
  have hfiber (H : Ideal O) (hH : H ∈ labels.image missing) :
      ((labels.filter (fun label => missing label = H)).card:ℝ) ≤ C*Z^loss := by
    obtain ⟨label₀,hl₀,hH₀⟩ := Finset.mem_image.mp hH
    have hH0 : H ≠ 0 := hH₀ ▸ hmissing0 label₀ hl₀
    let fibre := labels.filter (fun label => missing label = H)
    have hinj : Set.InjOn (fun label : FirstSourceLabel => label.1) (↑fibre : Set FirstSourceLabel) := by
      intro a ha b hb hab
      apply first_source_key_injective left
      exact Prod.ext hab ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hb := hpair Z hZ (Ideal.span {w}*H)
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hH0)
      (by simpa only [←hH₀] using hsupportnorm label₀ hl₀)
      (fibre.image (fun label => label.1))
      (by
        intro p hp
        obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hp
        exact ⟨(hnonzero label (Finset.mem_filter.mp hl).1).1.1,
          (hnonzero label (Finset.mem_filter.mp hl).1).2⟩)
      (by
        intro p hp
        obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hp
        exact heq label (Finset.mem_filter.mp hl).1)
      (by
        intro p hp
        obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hp
        have hh := first_source_literal_support left label
          (hnonzero label (Finset.mem_filter.mp hl).1).1
          (heq label (Finset.mem_filter.mp hl).1) w hw
          (hliteral label (Finset.mem_filter.mp hl).1)
        change primeSupport label.1.1 ⊆ primeSupport (Ideal.span {w}*missing label) at hh
        rwa [(Finset.mem_filter.mp hl).2] at hh)
      (by
        intro p hp
        obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hp
        exact hnorm label (Finset.mem_filter.mp hl).1)
    rwa [Finset.card_image_of_injOn hinj] at hb
  have hrad := Cycle63.Physical.missing_radical_card (labels.image missing) Z m
    (by linarith)
    (by intro H hH; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hH; exact hmissing0 label hl)
    (by intro H hH; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hH; exact hmissing label hl)
  have he := Finset.card_eq_sum_card_fiberwise
    (fun label (hl : label ∈ labels) => Finset.mem_image_of_mem missing hl)
  calc
    _ = ∑ H ∈ labels.image missing, ((labels.filter (fun label => missing label = H)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _H ∈ labels.image missing, C*Z^loss := Finset.sum_le_sum hfiber
    _ = ((labels.image missing).card:ℝ)*(C*Z^loss) := by simp
    _ ≤ (128*Z^m)*(C*Z^loss) := mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < Z)]; ring

#print axioms first_source_literal_support
#print axioms actual_first_source_row_count
end
end OAI.SevenEighths.Cycle63Moment
