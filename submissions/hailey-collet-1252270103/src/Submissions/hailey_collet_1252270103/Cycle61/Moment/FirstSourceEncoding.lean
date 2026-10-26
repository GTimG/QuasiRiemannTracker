import Submissions.hailey_collet_1252270103.Cycle61.Moment.CanonicalFirstSupport

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic
local notation "O" => HeckeFamily.O

/-- The inactive projector is recovered from the first common pair and the
missing radical. It introduces no additional fibre multiplicity. -/
theorem first_missing_radical_injOn (C D : Ideal O) (left : Bool) :
    Set.InjOn (fun E => firstMissingRadical C D E left) (inactiveSubsets C D) := by
  intro E hE F hF hrad
  have hm : firstMissingCommon C D E left = firstMissingCommon C D F left :=
    FirstCauchyArithmetic.family_product_injective
      (fun P : CommonIndex C D => P.val) Subtype.val_injective hrad
  have he := first_projector_retained_disjoint C D E hE left
  have hf := first_projector_retained_disjoint C D F hF left
  ext P
  have hh := Finset.ext_iff.mp hm P
  simp only [firstMissingCommon, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_union, true_and, not_or] at hh
  by_cases hp : P ∈ firstRetainedCommon C D left
  · have hnE := fun hEP => (Finset.disjoint_left.mp he hEP hp)
    have hnF := fun hFP => (Finset.disjoint_left.mp hf hFP hp)
    exact iff_of_false hnE hnF
  · simp only [hp, not_false_eq_true, and_true] at hh
    exact not_iff_not.mp hh

def FirstSourceLabel :=
  Σ CD : Ideal O × Ideal O,
    {E : Finset (CommonIndex CD.1 CD.2) // E ∈ inactiveSubsets CD.1 CD.2}

def firstSourceKey (left : Bool) (label : FirstSourceLabel) :
    (Ideal O × Ideal O) × Ideal O :=
  (label.1, firstMissingRadical label.1.1 label.1.2 label.2.val left)

theorem first_source_key_injective (left : Bool) : Function.Injective (firstSourceKey left) := by
  rintro ⟨CD, E⟩ ⟨CD', F⟩ h
  have hCD : CD = CD' := congrArg Prod.fst h
  cases hCD
  have hrad := congrArg Prod.snd h
  have hEF := first_missing_radical_injOn CD.1 CD.2 left E.property F.property hrad
  have hs : E = F := Subtype.ext hEF
  cases hs
  rfl

theorem first_source_label_card (left : Bool) (labels : Finset FirstSourceLabel) :
    labels.card ≤ (labels.image (fun label => label.1)).card *
      (labels.image (fun label => firstMissingRadical label.1.1 label.1.2 label.2.val left)).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (firstSourceKey left)
  · intro label hlabel
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨label,hlabel,rfl⟩,
      Finset.mem_image.mpr ⟨label,hlabel,rfl⟩⟩
  · exact (first_source_key_injective left).injOn

#print axioms first_missing_radical_injOn
#print axioms first_source_key_injective
#print axioms first_source_label_card
end
end OAI.SevenEighths.Cycle61Moment
