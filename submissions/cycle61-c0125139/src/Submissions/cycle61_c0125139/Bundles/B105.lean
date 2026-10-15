/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B103
import Submissions.cycle61_c0125139.Bundles.B104
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinRadical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency

/- BEGIN ORIGINAL Cycle61.Physical.SecondCommonRadical; sha256 4ac661978ca580bfa7d0ac175be2b7b7443936ea37454fb00ec92fb6d4df5cf1 -/
section
                                                                   
                                                        

namespace Cycle61.Physical

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths UniqueFactorizationMonoid
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentRankinRadical

local notation "O" => ActualEisensteinCubic.O

/-- Every prime in the common radical occurs in the actual extracted second
frequency, with its full minimum valuation. -/
theorem common_radical_dvd_frequency (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    commonRadical C D ∣ Ideal.span {commonFrequencyGenerator C D} := by
  have hrad : commonRadical C D = ∏ P : CommonIndex C D, P.val := by
    exact (Finset.prod_coe_sort
      (s := CenteredMomentCompleteCommon.commonSupport C D) (f := id)).symm
  rw [hrad, commonFrequencyGenerator, ← Ideal.prod_span_singleton]
  simp_rw [← Ideal.span_singleton_pow, commonPrime_span C D hC]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  have hm : 1 ≤ min (leftExponent C D P) (rightExponent C D P) :=
    le_min (leftExponent_pos C D P) (rightExponent_pos C D P)
  simpa only [pow_one] using pow_dvd_pow P.val hm

/-- The first squarefree projector has genuine divisibility provenance on both
second common ideals, so it also divides the extracted common frequency. -/
theorem first_projector_dvd_frequency (L C D : Ideal O) (hL : Squarefree L)
    (hC : CanonicalQuadraticSieve.Supported C) (hD : D ≠ 0)
    (hLC : L ∣ C) (hLD : L ∣ D) :
    L ∣ Ideal.span {commonFrequencyGenerator C D} :=
  (old_mask_dvd_commonRadical L C D hL hC.1 hD hLC hLD).trans
    (common_radical_dvd_frequency C D hC)

theorem prime_support_mono {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    IdealMobiusDivisorSum.primeSupport I ⊆ IdealMobiusDivisorSum.primeSupport J := by
  intro P hP
  have hp := IdealMobiusDivisorSum.support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  simpa only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff hJ, hp, true_and] using hd.trans hIJ

/-- Equal common supports are contained in the support of the literal row once
the actual common frequency divides that row. -/
theorem common_support_in_row (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C)
    (hCD : IdealMobiusDivisorSum.primeSupport C = IdealMobiusDivisorSum.primeSupport D)
    (w : O) (hw : w ≠ 0) (hGw : commonFrequencyGenerator C D ∣ w) :
    IdealMobiusDivisorSum.primeSupport C ⊆
      IdealMobiusDivisorSum.primeSupport (Ideal.span {w}) := by
  have hspan : Ideal.span {commonFrequencyGenerator C D} ∣ Ideal.span {w} := by
    obtain ⟨v, rfl⟩ := hGw
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact dvd_mul_right _ _
  have hs := prime_support_mono (Ideal.span_singleton_eq_bot.not.mpr hw)
    ((common_radical_dvd_frequency C D hC).trans hspan)
  rw [commonRadical_support, hCD, Finset.inter_self] at hs
  simpa only [hCD] using hs

end

end Cycle61.Physical

#print axioms Cycle61.Physical.common_radical_dvd_frequency
#print axioms Cycle61.Physical.first_projector_dvd_frequency
#print axioms Cycle61.Physical.common_support_in_row

end
/- END ORIGINAL Cycle61.Physical.SecondCommonRadical -/

/- BEGIN ORIGINAL Cycle61.Moment.JointSourceCount; sha256 a4ccf548beba71c2b237c45cf62febd97c7e36dbc67953fbbb8b1274918697c1 -/
section
                                          
                                           

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
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
  obtain ⟨C₂,hC₂,hsecond⟩ := Cycle61.Physical.uniform_common_pair_count B (loss/2) hB (by positivity)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro left u₀ unit Z hZ w hw hwnorm m labels hrow hnonzero heq hsupportnorm hnorm hmissing
  have hf := hfirst left Z hZ w hw m (labels.image (fun label => label.1))
    (by
      intro first hf
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(hnonzero label hl).1,(hnonzero label hl).2.1⟩)
    (by
      intro first hf
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf
      exact (heq label hl).1)
    (by
      intro first hf
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨u₀*unit label.1,commonFrequencyGenerator label.2.1.1 label.2.1.2,
        nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1,
        label.2.2.val.2,(hrow label hl).symm⟩)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact hsupportnorm label hl)
    (by
      intro first hf
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(hnorm label hl).1,(hnorm label hl).2.1⟩)
    (by intro first hf; obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hf; exact hmissing label hl)
  have hs := hsecond Z hZ (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw) hwnorm
    (labels.image (fun label => label.2.1))
    (by
      intro second hs
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs
      exact ⟨(hnonzero label hl).2.2.1.1,(hnonzero label hl).2.2.2⟩)
    (by
      intro second hs
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs
      exact (heq label hl).2)
    (by
      intro second hs
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs
      apply Cycle61.Physical.common_support_in_row _ _ (hnonzero label hl).2.2.1
        (heq label hl).2 w hw
      rw [←hrow label hl]
      exact joint_source_second_generator_dvd left u₀ unit label)
    (by
      intro second hs
      obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hs
      exact (hnorm label hl).2.2)
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
          ring

#print axioms joint_source_second_generator_dvd
#print axioms joint_source_fixed_row_pair_injOn
#print axioms actual_joint_source_row_count
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointSourceCount -/

/- BEGIN ORIGINAL Cycle61.Moment.JointHighDensity; sha256 4880e22bc15c5ce774b39c85abdf21561c958987ddb36cfbc79f80adc4daf875 -/
section
                                      
                                      

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

def NonzeroJointSourceLabel (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O) :=
  {label : JointSourceLabel // jointSourceRow left u₀ unit label ≠ 0}

def nonzeroJointSourceRow {left : Bool} {u₀ : O} {unit : FirstSourceLabel → O}
    (label : NonzeroJointSourceLabel left u₀ unit) : NonzeroFrequency :=
  ⟨jointSourceRow left u₀ unit label.val,label.property⟩

theorem actual_signed_zero_to_natural (η : Character)
    (puncture : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) →
      NonzeroFrequency → Ideal O)
    (reverse : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → Bool)
    (a T : ℝ) (ha : 0 < a) (w : NonzeroFrequency)
    (hz : maskedActualZeroRow (actualMaskedRowFamily η puncture) reverse a T w) :
    naturalActualZeroRow (secondFixedDictionary η) reverse a T w := by
  apply masked_zero_to_natural (secondFixedDictionary η) (actualMaskedRowFamily η puncture)
    _ reverse a T ha w hz
  intro j u I
  exact excludePrimes_mask _ _ (support_prime (puncture j u)) I

/-- The constants precede the live source labels, Euler punctures, both heights
and the bin position. Each missing radical and literal frequency is counted once. -/
theorem actual_joint_natural_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ reverse : Dict → Bool,
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        naturalActualZeroRow base reverse a T
          (nonzeroJointSourceRow label)) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  let δ := loss/(2*(Q+1))
  have hδ : 0 < δ := div_pos hloss (by positivity)
  obtain ⟨J,D,hD,hdensity⟩ := fixed_natural_dictionary_raw_density base δ hδ
  obtain ⟨C,hC,hcount⟩ := actual_joint_source_row_count B (loss/2) hB (by positivity)
  refine ⟨J,D*C,mul_pos hD hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels reverse hzero
    hnonzero heq hsupportnorm hnorm hmissing
  let row : NonzeroJointSourceLabel left u₀ unit → NonzeroFrequency := nonzeroJointSourceRow
  have hZ0 : 0 < Z := by linarith
  have hradius : 0 < Z^q := Real.rpow_pos_of_pos hZ0 q
  have hd := hdensity reverse a T ha ha' hT (Z^q) hradius (labels.image row) (by
    intro w hw
    obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hw
    exact hzero label hl)
  have hfiber (w : NonzeroFrequency) (hw : w ∈ labels.image row) :
      ((labels.filter (fun label => row label = w)).card:ℝ) ≤ C*Z^(m+loss/2) := by
    let fibre := labels.filter (fun label => row label = w)
    have mem_fibre (v : NonzeroJointSourceLabel left u₀ unit) (hv : v ∈ fibre) :
        v ∈ labels ∧ row v = w := by
      simpa only [fibre, Finset.mem_filter] using hv
    have hc := hcount left u₀ unit Z hZ w.val w.property
      (by
        obtain ⟨label,hl,hrow⟩ := Finset.mem_image.mp hw
        have hn := (hzero label hl).1
        change ((Ideal.span {jointSourceRow left u₀ unit label.val}).absNorm:ℝ) ≤ Z^q at hn
        have he : jointSourceRow left u₀ unit label.val = w.val := congrArg Subtype.val hrow
        rw [he] at hn
        exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (hq.trans hQB)))
      m (fibre.image Subtype.val)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        exact congrArg Subtype.val (mem_fibre v hv).2)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnonzero v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact heq v (mem_fibre v hv).1)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        have he : jointSourceRow left u₀ unit v.val = w.val :=
          congrArg Subtype.val (mem_fibre v hv).2
        simpa only [he] using hsupportnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hmissing v (mem_fibre v hv).1)
    have hinj : Set.InjOn (fun v : NonzeroJointSourceLabel left u₀ unit => v.val)
        (↑fibre : Set (NonzeroJointSourceLabel left u₀ unit)) :=
      fun v _ r _ h => Subtype.ext h
    have hcard : fibre.card ≤ (fibre.image Subtype.val).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv
        exact Finset.mem_image_of_mem _ hv
      · exact hinj
    change (fibre.card:ℝ) ≤ C*Z^(m+loss/2)
    exact (show (fibre.card:ℝ) ≤ ((fibre.image Subtype.val).card:ℝ) by exact_mod_cast hcard).trans hc
  have he := Finset.card_eq_sum_card_fiberwise
    (fun label (hl : label ∈ labels) => Finset.mem_image_of_mem row hl)
  have hbudget : q*δ ≤ loss/2 := by
    have hid : δ*(2*(Q+1)) = loss := by dsimp only [δ]; field_simp
    have hqδ := mul_le_mul_of_nonneg_right hq hδ.le
    nlinarith
  calc
    _ = ∑ w ∈ labels.image row, ((labels.filter (fun label => row label = w)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _w ∈ labels.image row, C*Z^(m+loss/2) := Finset.sum_le_sum hfiber
    _ = ((labels.image row).card:ℝ)*(C*Z^(m+loss/2)) := by simp
    _ ≤ (D*(1+T)^J*(Z^q)^(unmarkedDensity (2*a-1)+δ))*(C*Z^(m+loss/2)) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (D*C)*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss/2+q*δ) := by
      rw [←Real.rpow_mul hZ0.le]
      calc
        _ = (D*C)*(1+T)^J*(Z^(q*(unmarkedDensity (2*a-1)+δ))*Z^(m+loss/2)) := by ring
        _ = _ := by
          rw [←Real.rpow_add hZ0]
          congr 1
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (by positivity)

theorem actual_joint_high_row_count (η : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit →
        (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → NonzeroFrequency → Ideal O,
      ∀ reverse : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → Bool,
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        maskedActualZeroRow (actualMaskedRowFamily η (puncture label)) reverse a T
          (nonzeroJointSourceRow label)) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (secondFixedDictionary η) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels puncture reverse hzero
    hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels reverse
    (fun label hl => ⟨(hzero label hl).1,
      actual_signed_zero_to_natural η (puncture label) reverse a T
        (by linarith) (nonzeroJointSourceRow label) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

#print axioms actual_signed_zero_to_natural
#print axioms actual_joint_natural_high_row_count
#print axioms actual_joint_high_row_count
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointHighDensity -/

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalPhaseCharacter; sha256 133e0b5afbfc56823011085a84e077af8e5c7d2ac9c0c6333802784b96bb12f6 -/
section
                                              

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open ActualEisensteinCubic CenteredMomentCanonicalFirst RayFourExpansion
open CenteredMomentChildRows
open CenteredMomentFixedRay
open CenteredMomentFirstColumns
local notation "O" => HeckeFamily.O

theorem firstPhaseTable_mul (C D : Ideal O) (t : ActiveIndex C D → ℕ)
    (x y : RayRing) :
    firstPhaseTable C D t (x*y) = firstPhaseTable C D t x * firstPhaseTable C D t y := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      change firstPhaseTable C D t (Ideal.Quotient.mk _ (x*y)) =
        firstPhaseTable C D t (Ideal.Quotient.mk _ x) *
        firstPhaseTable C D t (Ideal.Quotient.mk _ y)
      simp only [firstPhaseTable_mk, sexticReciprocityPhase_mul_right, mul_pow,
        Finset.prod_mul_distrib]

def firstPhaseCharacter (C D : Ideal O) (hC : Supported C)
    (t : ActiveIndex C D → ℕ) : RayCharacter where
  toFun x := if IsUnit x then firstPhaseTable C D t x else 0
  map_one' := by
    rw [if_pos isUnit_one]
    change firstPhaseTable C D t (Ideal.Quotient.mk _ 1) = 1
    simp only [firstPhaseTable_mk, sexticReciprocityPhase_one_right _
      (firstSignedPrime_supported C D hC _), one_pow, Finset.prod_const_one]
  map_mul' x y := by
    by_cases hx : IsUnit x <;> by_cases hy : IsUnit y
    · simp only [if_pos hx, if_pos hy, if_pos (hx.mul hy), firstPhaseTable_mul]
    · have hxy : ¬IsUnit (x*y) := fun h => hy (isUnit_of_mul_isUnit_right h)
      simp only [if_pos hx, if_neg hy, if_neg hxy, mul_zero]
    · have hxy : ¬IsUnit (x*y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp only [if_neg hx, if_pos hy, if_neg hxy, zero_mul]
    · have hxy : ¬IsUnit (x*y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp only [if_neg hx, if_neg hy, if_neg hxy, zero_mul]
  map_nonunit' x hx := if_neg hx

theorem actual_first_phase_character (C D : Ideal O) (hC : Supported C)
    (t : ActiveIndex C D → ℕ) (n : O) (hn : Supported (Ideal.span {n})) :
    rayCharacter (firstPhaseCharacter C D hC t) n =
      ∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {(4:O)}) n) := by
    have hmask := supported_rayMask n hn
    unfold rayMask at hmask
    split_ifs at hmask with h
    · exact h
    · exact False.elim (by norm_num at hmask)
  change (if IsUnit (Ideal.Quotient.mk _ n) then firstPhaseTable C D t
    (Ideal.Quotient.mk _ n) else 0) = _
  rw [if_pos hunit, firstPhaseTable_mk]

theorem actual_first_left_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ u₀ e n : O, Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
        rayCharacter ξ n =
      elementCoeff (childCharacter η
        (firstPhaseCharacter C D hC (activeExponent C D)*ξ)) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_signed C D hC
  refine ⟨u,?_⟩
  intro u₀ e n hn hnp
  rw [hu e n hn hnp, ← actual_first_phase_character C D hC (activeExponent C D) n hn,
    idealRowHom_argument_mul, actual_first_left_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

theorem actual_first_right_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ u₀ e n : O, Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
        rayCharacter ξ n =
      elementCoeff (childCharacter η
        (firstPhaseCharacter C D hC (fun P => 6-activeExponent C D P)*ξ)) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_signed C D hC
  refine ⟨u,?_⟩
  intro u₀ e n hn hnp
  rw [hu e n hn hnp,
    ← actual_first_phase_character C D hC (fun P => 6-activeExponent C D P) n hn,
    idealRowHom_argument_mul, actual_first_right_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

#print axioms actual_first_phase_character
#print axioms actual_first_left_single_dictionary
#print axioms actual_first_right_single_dictionary
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalPhaseCharacter -/
