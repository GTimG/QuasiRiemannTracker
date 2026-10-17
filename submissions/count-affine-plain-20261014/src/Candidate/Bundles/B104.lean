/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B103
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinSubset
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal

/- BEGIN ORIGINAL Cycle61.Moment.FirstSourceEncoding; sha256 4edf77919104a0e79bd42679a094781eca886340e6fb9c5ac2799f7a8af8990f -/
section
                                           

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

end
/- END ORIGINAL Cycle61.Moment.FirstSourceEncoding -/

/- BEGIN ORIGINAL Cycle61.Physical.JointRowFibres; sha256 6ca353b424391be4df1ff18daff4b3e5e4920e6870bb178da1144172e7ed4271 -/
section
                                                       
                                                         

namespace Cycle61.Physical

open OAI OAI.SevenEighths OAI.IdealMobiusDivisorSum

noncomputable section

local notation "O" => ActualEisensteinCubic.O

/-- Uniform in the supporting ideal and in arbitrary valuations of both ideals. -/
theorem uniform_supported_pair_count (B epsilon : ℝ) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ N : Ideal O, N ≠ 0 →
      (Ideal.absNorm N : ℝ) ≤ Z ^ B → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S, v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1 ⊆ primeSupport N ∧ primeSupport v.2 ⊆ primeSupport N) →
      (∀ v ∈ S, (Ideal.absNorm v.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.2 : ℝ) ≤ Z ^ B) →
      (S.card : ℝ) ≤ C * Z ^ epsilon := by
  let a : ℝ := epsilon / (3 * (B + 1))
  have ha : 0 < a := div_pos he (by positivity)
  obtain ⟨C, hC, hcount⟩ := CenteredMomentRankinSubset.supported_power_pair_count a a ha ha
  refine ⟨C, hC, ?_⟩
  intro Z hZ N hN0 hN S hS hs hnorm
  have hZ0 : 0 < Z := by linarith
  have hZB : 0 < Z ^ B := Real.rpow_pos_of_pos hZ0 B
  have hbound := hcount N hN0 S hS hs (Z ^ B) (Z ^ B) hZB hZB hnorm
  have hsupport := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm N)) hN ha.le
  have hexponent : B * a + B * a + B * a ≤ epsilon := by
    have hid : a * (3 * (B + 1)) = epsilon := by dsimp only [a]; field_simp
    nlinarith
  calc
    (S.card : ℝ) ≤ C * (Z ^ B) ^ a * (Z ^ B) ^ a * (Ideal.absNorm N : ℝ) ^ a := hbound
    _ ≤ C * (Z ^ B) ^ a * (Z ^ B) ^ a * (Z ^ B) ^ a :=
      mul_le_mul_of_nonneg_left hsupport (by positivity)
    _ = C * Z ^ (B * a + B * a + B * a) := by
      rw [← Real.rpow_mul hZ0.le]
      rw [Real.rpow_add hZ0, Real.rpow_add hZ0]
      ring
    _ ≤ C * Z ^ epsilon := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hexponent) hC.le

/-- The equal-support interface used by the joint common-ideal fibres. -/
theorem uniform_common_pair_count (B epsilon : ℝ) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ N : Ideal O, N ≠ 0 →
      (Ideal.absNorm N : ℝ) ≤ Z ^ B → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S, v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1 = primeSupport v.2) →
      (∀ v ∈ S, primeSupport v.1 ⊆ primeSupport N) →
      (∀ v ∈ S, (Ideal.absNorm v.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.2 : ℝ) ≤ Z ^ B) →
      (S.card : ℝ) ≤ C * Z ^ epsilon := by
  obtain ⟨C, hC, hcount⟩ := uniform_supported_pair_count B epsilon hB he
  refine ⟨C, hC, ?_⟩
  intro Z hZ N hN0 hN S hS heq hs hnorm
  apply hcount Z hZ N hN0 hN S hS _ hnorm
  intro v hv
  refine ⟨hs v hv, ?_⟩
  rw [← heq v hv]
  exact hs v hv

/-- The missing-radical count needs only nonzero ideals and a norm upper bound. -/
theorem missing_radical_card (S : Finset (Ideal O)) (Z m : ℝ) (hZ : 0 ≤ Z)
    (hS : ∀ I ∈ S, I ≠ 0) (hnorm : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ m) :
    (S.card : ℝ) ≤ 128 * Z ^ m := by
  have hb := CenteredMomentSecondDiagonal.divisible_ideal_card S (1 : Ideal O)
    (by simp) hS (fun I _ => one_dvd I) (Z ^ m) (Real.rpow_nonneg hZ m) hnorm
  simpa using hb

end

end Cycle61.Physical

#print axioms Cycle61.Physical.uniform_supported_pair_count
#print axioms Cycle61.Physical.uniform_common_pair_count
#print axioms Cycle61.Physical.missing_radical_card

end
/- END ORIGINAL Cycle61.Physical.JointRowFibres -/

/- BEGIN ORIGINAL Cycle61.Moment.FirstSourceCount; sha256 57ebe667720b82f184268e2ac6458218f368ef6fee7079bb95a3656d966169ff -/
section
                                         
                                      

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
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
  obtain ⟨C,hC,hpair⟩ := Cycle61.Physical.uniform_common_pair_count B loss hB hloss
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
  have hrad := Cycle61.Physical.missing_radical_card (labels.image missing) Z m
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
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.FirstSourceCount -/

/- BEGIN ORIGINAL Cycle61.Moment.SecondSourceEncoding; sha256 d7aeabf08e66a39caebab48752161f6d75a4916308e63bf98b00b62afab00d6e -/
section
                                      
                                                                 

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSupport
open CenteredMomentSecondLedger
local notation "O" => HeckeFamily.O

def SecondSourceFrequency (C D : Ideal O) :=
  {q : Finset (CommonIndex C D) × O //
    canonicalPartition C D q.1 (nonunitFrequencyGenerator C D q.1*q.2)}

def secondSourceFrequency (C D : Ideal O) (q : SecondSourceFrequency C D) : O :=
  nonunitFrequencyGenerator C D q.val.1*q.val.2

/-- The actual partition is determined by its pre-split frequency; after it
is known, cancellation recovers the residual frequency. -/
theorem second_source_frequency_injective (C D : Ideal O) (hC : Supported C) :
    Function.Injective (secondSourceFrequency C D) := by
  intro q r h
  have hU : q.val.1 = r.val.1 := q.property.symm.trans
    ((congrArg (fun z => actualUnitSet (commonPrime C D)
      (leftExponent C D) (rightExponent C D) z) h).trans r.property)
  apply Subtype.ext
  apply Prod.ext hU
  change nonunitFrequencyGenerator C D q.val.1*q.val.2 =
    nonunitFrequencyGenerator C D r.val.1*r.val.2 at h
  rw [←hU] at h
  exact mul_left_cancel₀ (nonunitFrequencyGenerator_ne_zero C D hC q.val.1) h

def JointSourceLabel :=
  Σ _first : FirstSourceLabel, Σ second : Ideal O × Ideal O,
    SecondSourceFrequency second.1 second.2

def jointSourceRow (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (label : JointSourceLabel) : O :=
  effectiveRow (u₀*unit label.1)
    (primeSubsetGenerator (fun P : CommonIndex label.1.1.1 label.1.1.2 => P.val) label.1.2.val)
    (firstSourceNumerator left label.1)
    (commonFrequencyGenerator label.2.1.1 label.2.1.2)
    (nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1) label.2.2.val.2

def jointSourceKey (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (label : JointSourceLabel) : O × (((Ideal O × Ideal O) × Ideal O) × (Ideal O × Ideal O)) :=
  (jointSourceRow left u₀ unit label, (firstSourceKey left label.1,label.2.1))

theorem joint_source_key_injOn (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (labels : Set JointSourceLabel)
    (hrow : ∀ label ∈ labels, jointSourceRow left u₀ unit label ≠ 0)
    (hsupported : ∀ label ∈ labels, Supported label.2.1.1) :
    Set.InjOn (jointSourceKey left u₀ unit) labels := by
  rintro ⟨first,CD,q⟩ ha ⟨first',CD',r⟩ hb hkey
  have hf : first = first' := first_source_key_injective left
    (congrArg (fun x => x.2.1) hkey)
  cases hf
  have hp : CD = CD' := congrArg (fun x => x.2.2) hkey
  cases hp
  have hw := congrArg Prod.fst hkey
  have hrowa := hrow _ ha
  let rowFactor := (u₀*unit first)*
    primeSubsetGenerator (fun P : CommonIndex first.1.1 first.1.2 => P.val) first.2.val*
    firstSourceNumerator left first*commonFrequencyGenerator CD.1 CD.2
  have heq (s : SecondSourceFrequency CD.1 CD.2) :
      jointSourceRow left u₀ unit ⟨first,CD,s⟩ = rowFactor*secondSourceFrequency CD.1 CD.2 s := by
    dsimp [jointSourceRow, rowFactor, effectiveRow, secondSourceFrequency]
    ring
  rw [heq] at hrowa
  have hprefix := (mul_ne_zero_iff.mp hrowa).1
  have hfreq : secondSourceFrequency CD.1 CD.2 q = secondSourceFrequency CD.1 CD.2 r := by
    apply mul_left_cancel₀ hprefix
    change jointSourceRow left u₀ unit ⟨first,CD,q⟩ =
      jointSourceRow left u₀ unit ⟨first,CD,r⟩ at hw
    simpa only [heq] using hw
  have hqr := second_source_frequency_injective CD.1 CD.2 (hsupported _ ha) hfreq
  cases hqr
  rfl

#print axioms second_source_frequency_injective
#print axioms joint_source_key_injOn
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.SecondSourceEncoding -/
