/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B096
import Candidate.Bundles.B101
import Candidate.Bundles.B103
import Candidate.Bundles.B105
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowPuncture

/- BEGIN ORIGINAL Cycle61.Moment.PrimaryMaskTransport; sha256 1ac16862f7bdd14845689d8de2ff498aea52201267337910fff7eee032ef363d -/
section
                                             
                                           
                                                       

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ProbePhysical CenteredMomentFixedRay
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- Primary-element identities determine every ideal coefficient after the
actual displayed Euler mask is restored. -/
theorem ideal_coefficient_mask_of_primary (χ ψ : Character)
    (hperiod : χ.modulus ≤ Ideal.span {(72:O)})
    (hprimary : ∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      IsCoprime (Ideal.span {n}) χ.modulus → elementCoeff χ n = elementCoeff ψ n)
    (I : Ideal O) :
    idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  by_cases hI : I = 0
  · simp only [hI, idealCoeff_zero, ite_self]
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc]
    let n : O := idealGenerator I
    have hn : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hn72 : IsCoprime n (72:O) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [hspan]
      exact hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hperiod)
    have hsup : Supported I := by
      rw [← hspan]
      apply supported_of_coprime_bad (72:O) n _ _ hn72.symm
      · exact (dvd_pow_self goodLambda (by decide : (2:ℕ) ≠ 0)).trans
          (ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨24,by norm_num⟩)
      · exact ⟨36,by norm_num⟩
    have hp0 := supported_primaryGenerator_ne_zero I hsup
    have hp := primaryGenerator_spec I hp0
    have hs : Supported (Ideal.span {primaryGenerator I}) := by rw [hp.1]; exact hsup
    have hc' : IsCoprime (Ideal.span {primaryGenerator I}) χ.modulus := by
      rw [hp.1]; exact hc
    have he := hprimary (primaryGenerator I) hs hp.2 hc'
    rwa [← idealCoeff_span χ hp0, ← idealCoeff_span ψ hp0, hp.1] at he
  · have hh := idealCoeff_source_mask χ I
    simpa only [ite_eq_right hc] using hh

theorem natural_row_supported_element (η : Character) (z n : O)
    (F : NaturalRow η z) (hn : Supported (Ideal.span {n})) :
    elementCoeff F.character n = elementCoeff η n * idealRowHom z (Ideal.span {n}) := by
  rw [F.element, rowTwist_extract_sixth_mask _ fixedBadMask 1 z n hn]
  change elementCoeff η n * coprimalityMask fixedBadMask n *
    idealRowHom (1^4*z) (Ideal.span {n}) = _
  rw [show coprimalityMask fixedBadMask n = (1:ℂ) by
    exact ite_eq_left (fixedBadMask_coprime n hn)]
  simp only [one_pow, one_mul, mul_one]

theorem natural_row_mask_of_primary (η χ : Character) (z : O)
    (F : NaturalRow η z) (hperiod : χ.modulus ≤ Ideal.span {(72:O)})
    (hprimary : ∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      IsCoprime (Ideal.span {n}) χ.modulus →
      elementCoeff χ n = elementCoeff η n * idealRowHom z (Ideal.span {n}))
    (I : Ideal O) :
    idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  apply ideal_coefficient_mask_of_primary χ F.character hperiod
  intro n hn hp hc
  rw [hprimary n hn hp hc, natural_row_supported_element η z n F hn]

theorem natural_parent_supported_element (η : Character) (z n : O)
    (F : NaturalRow η z) (R : Ideal O) (hn : Supported (Ideal.span {n}))
    (hc : IsCoprime (Ideal.span {n}) (excluded F.character R).modulus) :
    elementCoeff (excluded F.character R) n =
      elementCoeff η n * idealRowHom z (Ideal.span {n}) := by
  have hn0 : n ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  rw [← idealCoeff_span _ hn0]
  change idealCoeff (F.character.excludePrimes (primeSupport R) (support_prime R))
    (Ideal.span {n}) = _
  change IsCoprime (Ideal.span {n})
    (F.character.excludePrimes (primeSupport R) (support_prime R)).modulus at hc
  rw [excludePrimes_mask, ite_eq_left hc, idealCoeff_span F.character hn0]
  exact natural_row_supported_element η z n F hn

theorem natural_row_supported_ideal (η : Character) (z : O) (F : NaturalRow η z)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff F.character I = idealCoeff η I * idealRowHom z I := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primaryGenerator_spec I hn
  rw [← hs.1, idealCoeff_span F.character hn, idealCoeff_span η hn]
  exact natural_row_supported_element η z _ F (by rw [hs.1]; exact hI)

theorem natural_row_ideal_zero_of_not_supported (η : Character) (z : O)
    (F : NaturalRow η z) (I : Ideal O) (hI : ¬Supported I) :
    idealCoeff F.character I = 0 := by
  by_cases hz : I = 0
  · rw [hz, idealCoeff_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I hz
  have hs : Ideal.span {n} = I := span_idealGenerator I
  rw [← hs, idealCoeff_span F.character hn, F.element]
  exact rowTwist_zero_of_not_supported _ _ _ _ _
    (dvd_mul_right _ _) (dvd_mul_left _ _) (by rwa [hs])

#print axioms ideal_coefficient_mask_of_primary
#print axioms natural_row_supported_element
#print axioms natural_row_mask_of_primary
#print axioms natural_parent_supported_element
#print axioms natural_row_supported_ideal
#print axioms natural_row_ideal_zero_of_not_supported
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.PrimaryMaskTransport -/

/- BEGIN ORIGINAL Cycle61.Moment.SecondNaturalMask; sha256 dfcbaa72801c4538b0ce69f1999c4e0f2070128a9325bb1c13db1687610d66ea -/
section
                                          
                                      

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentChildRows CenteredMomentNaturalRowSource RayFourExpansion
local notation "O" => HeckeFamily.O

theorem actual_second_natural_mask (η χ : Character) (w A : O)
    (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A)) (I : Ideal O) :
    idealCoeff child.character I = idealCoeff (excluded final.character χ.modulus) I := by
  by_cases hs : Supported I
  · rw [natural_row_supported_ideal _ _ child I hs,
      childCharacter, idealCoeff_product, hmask I,
      natural_row_supported_ideal _ _ F I hs,
      excluded_ideal _ _ χ.modulus_ne_bot,
      natural_row_supported_ideal _ _ final I hs,
      childCharacter, idealCoeff_product, idealRowHom_argument_mul]
    by_cases hc : IsCoprime I χ.modulus <;> simp only [hc, ite_true, ite_false] <;> ring
  · rw [natural_row_ideal_zero_of_not_supported _ _ child I hs,
      excluded_ideal _ _ χ.modulus_ne_bot,
      natural_row_ideal_zero_of_not_supported _ _ final I hs]
    split_ifs <;> rfl

theorem actual_second_punctured_natural_mask (η χ : Character) (w A : O)
    (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A))
    (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded child.character R) I =
      idealCoeff (excluded final.character (χ.modulus*R)) I := by
  rw [excluded_ideal _ _ hR, actual_second_natural_mask η χ w A F hmask ξ child final I,
    excluded_ideal _ _ χ.modulus_ne_bot,
    excluded_ideal _ _ (mul_ne_zero χ.modulus_ne_bot hR), IsCoprime.mul_right_iff]
  by_cases hc : IsCoprime I χ.modulus <;> by_cases hr : IsCoprime I R <;>
    simp only [hc, hr, and_self, true_and, false_and, ite_true, ite_false]

theorem actual_fixed_product_natural_mask (η χ ν : Character) (w : O)
    (F : NaturalRow η w) (G : NaturalRow (η.product ν) w)
    (R : Ideal O) (hR : R ≠ 0)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff (excluded F.character R) I)
    (I : Ideal O) :
    idealCoeff (χ.product ν) I = idealCoeff (excluded G.character R) I := by
  rw [idealCoeff_product, hcoeff I, excluded_ideal _ _ hR,
    excluded_ideal _ _ hR, F.ideal I, G.ideal I, idealCoeff_product]
  split_ifs <;> ring

#print axioms actual_second_natural_mask
#print axioms actual_second_punctured_natural_mask
#print axioms actual_fixed_product_natural_mask
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.SecondNaturalMask -/

/- BEGIN ORIGINAL Cycle61.Moment.PhysicalHighRows; sha256 861aaae228496cac60dda92a895243e8dfe3a89279b2d284e6391d14e3b5029d -/
section
                                      
                                       

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily LocalMoment ProbePhysical CenteredMomentNaturalRowSource
open CanonicalQuadraticSieve IdealMobiusDivisorSum
open RayFourExpansion
local notation "O" => HeckeFamily.O

abbrev OrientedSecondDictionary := (RayCharacter × RayCharacter) × Bool

def orientedSecondBase (η : Character) (j : OrientedSecondDictionary) : Character :=
  secondFixedDictionary η j.1

def wholeOrientation (χ : Character) (reverse : Bool) : Character :=
  if reverse then χ.inverse else χ

theorem whole_orientation_coefficients (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) (reverse : Bool) :
    ∀ I : Ideal O, idealCoeff (wholeOrientation χ reverse) I =
      idealCoeff (wholeOrientation ψ reverse) I := by
  intro I
  cases reverse
  · exact hcoeff I
  · change idealCoeff χ.inverse I = idealCoeff ψ.inverse I
    rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj, hcoeff I]

def orientedFixedBase {Dict : Type*} (base : Dict → Character) (j : Dict × Bool) : Character :=
  base j.1

/-- This transfers zeros of the literal second character, rather than zeros
of a Fourier summand. The Euler deletion and whole orientation are retained. -/
theorem physical_zero_to_fixed_dictionary {Dict : Type*} (base : Dict → Character)
    (χ : Character) (j : Dict) (w : NonzeroFrequency)
    (R : Ideal O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I =
      idealCoeff (excluded (naturalRow (base j) w.val w.property).character R) I)
    (a T : ℝ) (ha : 0 < a)
    (hz : ∃ s : ℂ, LFunction (wholeOrientation χ reverse) s = 0 ∧
      (s ≠ 1 ∨ (wholeOrientation χ reverse).residue ≠ 1) ∧
      a ≤ s.re ∧ |s.im| ≤ T) :
    naturalActualZeroRow (orientedFixedBase base) Prod.snd a T w := by
  obtain ⟨s,hzero,hpole,hs,ht⟩ := hz
  let F := (naturalRow (base j) w.val w.property).character
  let ψ := excluded F R
  have he := positive_zeros_eq_of_coefficients (wholeOrientation χ reverse)
    (wholeOrientation ψ reverse)
    (whole_orientation_coefficients χ ψ hcoeff reverse) (ha.trans_le hs) hpole
  have hm : ∀ I : Ideal O, idealCoeff (wholeOrientation ψ reverse) I =
      if IsCoprime I (wholeOrientation ψ reverse).modulus then
        idealCoeff (wholeOrientation F reverse) I else 0 := by
    have hb : ∀ I : Ideal O, idealCoeff ψ I =
        if IsCoprime I ψ.modulus then idealCoeff F I else 0 :=
      fun I => excludePrimes_mask F _ (support_prime R) I
    cases reverse
    · exact hb
    · exact inverse_coefficient_mask ψ F hb
  have hp := positive_zeros_eq_of_mask_nonpole
    (wholeOrientation ψ reverse) (wholeOrientation F reverse) hm
    (ha.trans_le hs) he.2
  refine ⟨(j,reverse),s,?_,?_,hs,ht⟩
  · exact hp.1.mp (he.1.mp hzero)
  · exact hp.2

/-- A genuine high-bin maximum supplies a positive nonpole zero of the
fixed natural dictionary. The live whole-character family and all moving
Euler holes remain literal through maximum attainment and zero transfer. -/
theorem physical_family_maximum_to_fixed_dictionary
    {Dict Family : Type*} [Fintype Family] (base : Dict → Character)
    (character : Family → Character) (reverse : Family → Bool)
    (hchar : ∀ j, (wholeOrientation (character j) (reverse j)).residue ≠ 1)
    (dictionary : Family → Dict) (puncture : Family → Ideal O)
    (w : NonzeroFrequency)
    (hcoeff : ∀ j, ∀ I : Ideal O, idealCoeff (character j) I =
      idealCoeff (excluded (naturalRow (base (dictionary j)) w.val w.property).character
        (puncture j)) I)
    (a T : ℝ) (ha : 51/100 < a)
    (hmax : a ≤ HeckeDetectorZeros.zeroMaximum
      (fun j => wholeOrientation (character j) (reverse j)) hchar T) :
    naturalActualZeroRow (orientedFixedBase base) Prod.snd a T w := by
  obtain ⟨j,s,hzero,hheight,hre⟩ := HeckeDetectorZeros.maximum_attained
    (fun j => wholeOrientation (character j) (reverse j)) hchar T (ha.trans_le hmax)
  exact physical_zero_to_fixed_dictionary base (character j) (dictionary j) w
    (puncture j) (reverse j) (hcoeff j) a T (by linarith)
    ⟨s,hzero,Or.inr (hchar j),by rw [hre]; exact hmax,hheight⟩

theorem physical_second_zero_to_dictionary (η χ : Character)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency)
    (R : Ideal O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I =
      idealCoeff (excluded (naturalRow (secondFixedDictionary η j) w.val w.property).character R) I)
    (a T : ℝ) (ha : 0 < a)
    (hz : ∃ s : ℂ, LFunction (wholeOrientation χ reverse) s = 0 ∧
      (s ≠ 1 ∨ (wholeOrientation χ reverse).residue ≠ 1) ∧
      a ≤ s.re ∧ |s.im| ≤ T) :
    naturalActualZeroRow (orientedSecondBase η) Prod.snd a T w := by
  exact physical_zero_to_fixed_dictionary (secondFixedDictionary η) χ j w R reverse
    hcoeff a T ha hz

theorem actual_joint_fixed_physical_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Bool,
      (∀ label ∈ labels, ∀ I : Ideal O, idealCoeff (character label) I =
        idealCoeff (excluded (naturalRow (base (dictionary label))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        ∃ s : ℂ, LFunction (wholeOrientation (character label) (reverse label)) s = 0 ∧
          (s ≠ 1 ∨ (wholeOrientation (character label) (reverse label)).residue ≠ 1) ∧
          a ≤ s.re ∧ |s.im| ≤ T) →
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
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels character dictionary
    puncture reverse hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_zero_to_fixed_dictionary base (character label) (dictionary label)
        (nonzeroJointSourceRow label) (puncture label) (reverse label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

/-- High-bin cardinality from the actual finite whole-family zero maximum,
with constants chosen before every live masked family and height. -/
theorem actual_joint_buffered_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ {Family : Type*} [Fintype Family],
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Family → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Family → Bool,
      ∀ hchar : ∀ label, ∀ j,
        (wholeOrientation (character label j) (reverse label j)).residue ≠ 1,
      (∀ label ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff (character label j) I =
        idealCoeff (excluded (naturalRow (base (dictionary label j))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label j)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (fun j => wholeOrientation (character label j) (reverse label j)) (hchar label) T) →
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
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels Family _ character dictionary
    puncture reverse hchar hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_family_maximum_to_fixed_dictionary base (character label) (reverse label)
        (hchar label) (dictionary label) (puncture label) (nonzeroJointSourceRow label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

theorem actual_joint_physical_high_row_count (η : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → RayCharacter × RayCharacter,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Bool,
      (∀ label ∈ labels, ∀ I : Ideal O, idealCoeff (character label) I =
        idealCoeff (excluded (naturalRow (secondFixedDictionary η (dictionary label))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        ∃ s : ℂ, LFunction (wholeOrientation (character label) (reverse label)) s = 0 ∧
          (s ≠ 1 ∨ (wholeOrientation (character label) (reverse label)).residue ≠ 1) ∧
          a ≤ s.re ∧ |s.im| ≤ T) →
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
  exact actual_joint_fixed_physical_high_row_count (secondFixedDictionary η)
    B Q loss hB hQ hQB hloss

#print axioms actual_joint_buffered_high_row_count
#print axioms physical_family_maximum_to_fixed_dictionary
#print axioms physical_zero_to_fixed_dictionary
#print axioms actual_joint_fixed_physical_high_row_count
#print axioms physical_second_zero_to_dictionary
#print axioms actual_joint_physical_high_row_count
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.PhysicalHighRows -/

/- BEGIN ORIGINAL Cycle61.Moment.HighSourceEnergy; sha256 25e3b32d16c558f51d64babf9ea8f0df44a9c73d4e277cf83c4def46037f123b -/
section
                                    
                                      

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros LocalMoment
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

structure HighSourceParameters where
  Wslot : ℝ → ℂ
  (A₀ B₀ : ℝ)
  hA₀ : 0 < A₀
  hWs : Function.support Wslot ⊆ Icc A₀ B₀
  hW : ContDiff ℝ ∞ Wslot
  (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax : ℝ)
  (bΦ Mcap Bmask margin d : ℝ)
  hRw : 0 ≤ Rwidth
  hRp : 0 ≤ Rplain
  hdmax : 0 ≤ dmax
  hτ : 0 < τ
  hεs : 0 < εslot
  hεp : 0 < εplain
  he : 0 < e
  he' : e < 1/1000
  hκ : 0 < κ
  hκ' : κ ≤ 1
  hvp : 0 ≤ vplain
  hvs : 0 ≤ vslot
  hslotBudget : 8*e*Rwidth+κ ≤ εslot
  hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain
  hbΦ : 0 ≤ bΦ
  hmargin : 0 < margin
  hd : 0 < d
  hdsupply : Mcap+Bmask+margin ≤ d
  hdm : d ≤ dmax
  profileBound : ℕ → ℝ
  hprofile : ∀ k, 0 ≤ profileBound k

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A dependent index retains the literal live slot type of each source.
Its analytic requirements below are structural, buffered-zero and profile gates. -/
structure HighSourceDatum (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (Dict : Type*) [Fintype Dict] where
  state : NaturalState Z P.Bmask P.bΦ
  hQM : state.fixedModulus ≤ M
  hQη : state.fixedModulus ≤ η₀.modulus
  z : O
  hz : state.radial.keep z
  natural : NaturalRow state.character z
  character : Dict → Character
  hcharacter : ∀ j, (character j).residue ≠ 1
  member : Dict
  Slot : Type
  [slotFintype : Fintype Slot]
  [slotDecidableEq : DecidableEq Slot]
  source : Data Slot
  second : Bool
  projector : Ideal O
  allocation : Allocation projector (Finset.univ : Finset (Slot ⊕ Fin 2))
  (w σ v : Slot → ℝ)
  θ : Slot → RayQuotient.Characters M H
  t : ℝ
  W : Fin 2 → ℝ → ℂ
  (X r A B : Fin 2 → ℝ)

attribute [instance] HighSourceDatum.slotFintype HighSourceDatum.slotDecidableEq

variable {M H}
variable {Dict : Type*} [Fintype Dict]

def HighSourceDatum.total (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℝ :=
  (∑ j, Real.logb Z (clippedScale
    (Cycle61.Physical.sourcePlainScales D.source.toSource D.second j)))+
    (∑ k, D.w k)-Cycle61.Physical.clippedReduction
      (Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P))
      (fun j => Real.logb Z (Cycle61.Physical.sourcePlainScales D.source.toSource D.second j))
      (Cycle61.Physical.actualPlainReduction Z D.projector D.allocation)

def HighSourceDatum.liveCard (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℕ :=
  (liveIndices D.projector D.allocation).card

def HighSourceDatum.row (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℂ :=
  Cycle61.Physical.sourcePositiveRow D.source.toSource D.second D.projector D.allocation D.z

structure HighSourceAdmissible (P : HighSourceParameters) (η₀ : Character) (Z a : ℝ)
    (i n : ℕ) (D : HighSourceDatum M H P η₀ Z Dict) : Prop where
  width : D.state.width ≤ P.Mcap
  low : ActualLow M H hH D.state η₀ D.hQM D.hQη a P.e
    (3*(i+1 : ℕ)*Z^P.τ) D.z
  member : D.character D.member = excluded D.natural.character D.state.puncture
  upper : zeroMaximum D.character D.hcharacter (3*(i+1 : ℕ)*Z^P.τ) < a+2*P.e
  modulus : (D.character D.member).modulus.absNorm ≤ Z^P.d
  character : D.source.η = D.state.character
  mask : D.source.m = D.state.mask
  A : D.source.A = 1
  height : D.source.t = D.t
  pool : ∀ k, D.source.slots k = primePool M H P.B₀ (Z^(D.w k))
  coefficient : ∀ k I, D.source.coefficient k I =
    idealCoeff (relativeCharacter M H hH η₀ (D.θ k)) I*
      annularWeight P.Wslot (Z^(D.w k)) (D.σ k) (D.v k) I
  scale : ∀ k, D.source.P k = Z^(D.w k)
  w_nonneg : ∀ k, 0 ≤ D.w k
  w_bound : ∀ k, D.w k/P.d ≤ P.Rwidth
  σ_lower : ∀ k, P.σmin ≤ D.σ k
  σ_upper : ∀ k, D.σ k ≤ P.σmax
  slot_frequency : ∀ k, |D.t+D.v k|+Z^P.τ/2 ≤ (3*i+2 : ℕ)*Z^P.τ
  slot_height : (3+(3*i+2 : ℕ)*Z^P.τ)^2 ≤ (Z^P.d)^P.vslot
  plain_frequency : |D.t|+Z^P.τ/2 ≤ (3*i+2 : ℕ)*Z^P.τ
  plain_height : (3+(3*i+2 : ℕ)*Z^P.τ)^4 ≤ (Z^P.d)^P.vplain
  W₁ : D.source.W₁ = D.W 0
  W₂ : D.source.W₂ = D.W 1
  post_scale : ∀ k, Cycle61.Physical.postPlainScale D.projector D.allocation
    (Cycle61.Physical.sourcePlainScales D.source.toSource D.second) k = D.X k
  X_pos : ∀ k, 0 < D.X k
  clipped_scale : ∀ k, clippedScale (D.X k) = (Z^P.d)^(D.r k)
  A_pos : ∀ k, 0 < D.A k
  support : ∀ k, Function.support (dilated (D.W k) (clipDilation (D.X k))) ⊆ Icc (D.A k) (D.B k)
  smooth : ∀ k, ContDiff ℝ ∞ (dilated (D.W k) (clipDilation (D.X k)))
  r_nonneg : ∀ k, 0 ≤ D.r k
  r_bound : ∀ k, D.r k ≤ P.Rplain
  mellin₂ : ∀ k, ∀ x ∈ Icc (1-a-6*P.e) 2, ∀ u : ℝ,
    (1+|u|)^2*‖mellin (dilated (D.W k) (clipDilation (D.X k)))
      ((x : ℂ)+u*Complex.I)‖ ≤ P.profileBound 2
  mellin_n : ∀ k, ∀ x ∈ Icc (1-a-6*P.e) 2, ∀ u : ℝ,
    (1+|u|)^(n+2)*‖mellin (dilated (D.W k) (clipDilation (D.X k)))
      ((x : ℂ)+u*Complex.I)‖ ≤ P.profileBound (n+2)

variable (M H)

theorem actual_high_source_datum (P : HighSourceParameters) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 → ∀ i : ℕ,
      ∀ {Dict : Type*} [Fintype Dict] (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D →
        ‖D.row P‖^2 ≤ Cp^2*Cs^(D.liveCard P)*
          Z^((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P)) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hrow⟩ := actual_high_source_row M H hH
    P.Wslot P.A₀ P.B₀ P.hA₀ P.hWs P.hW
    P.Rwidth P.Rplain P.dmax P.τ P.εslot P.εplain P.e P.κ P.vplain P.vslot
    P.σmin P.σmax P.bΦ P.Mcap P.Bmask P.margin P.d
    P.hRw P.hRp P.hdmax P.hτ P.hεs P.hεp P.he P.he' P.hκ P.hκ' P.hvp P.hvs
    P.hslotBudget P.hplainBudget P.hbΦ P.hmargin P.hd P.hdsupply P.hdm
    P.profileBound P.hprofile
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hrow η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Dict _ D hD
  exact hZ.2 D.state hD.width D.hQM D.hQη a i ha ha' D.z D.hz D.natural hD.low
    D.character D.hcharacter D.member hD.member hD.upper hD.modulus
    D.w D.σ D.v D.θ D.t D.source D.second D.projector D.allocation
    hD.character hD.mask hD.A hD.height hD.pool hD.coefficient hD.scale hD.w_nonneg
    hD.w_bound hD.σ_lower hD.σ_upper hD.slot_frequency hD.slot_height
    hD.plain_frequency hD.plain_height D.W D.X D.r D.A D.B hD.W₁ hD.W₂
    hD.post_scale hD.X_pos hD.clipped_scale hD.A_pos hD.support hD.smooth
    hD.r_nonneg hD.r_bound hD.mellin₂ hD.mellin_n

theorem high_source_datum_cap (P : HighSourceParameters) {η₀ : Character} {Z a : ℝ}
    {D : HighSourceDatum M H P η₀ Z Dict} {Cp Cs E : ℝ} {N : ℕ}
    (hZ : 1 ≤ Z) (hCs : 0 ≤ Cs) (ha : 1/2 ≤ a)
    (hrow : ‖D.row P‖^2 ≤ Cp^2*Cs^(D.liveCard P)*
      Z^((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P)))
    (hwidth : D.total P ≤ E) (hcard : D.liveCard P ≤ N) :
    ‖D.row P‖^2 ≤ Cp^2*(max 1 Cs)^N*
      Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  have hCp : 0 ≤ Cp^2 := sq_nonneg Cp
  have hpow : Cs^(D.liveCard P) ≤ (max 1 Cs)^N :=
    (pow_le_pow_left₀ hCs (le_max_right 1 Cs) _).trans
      (pow_le_pow_right₀ (le_max_left 1 Cs) hcard)
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hcardR : (D.liveCard P : ℝ) ≤ N := by exact_mod_cast hcard
  have hε : 0 ≤ 2*P.εslot*P.d :=
    mul_nonneg (mul_nonneg (by norm_num) P.hεs.le) P.hd.le
  have hexp : (2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P) ≤
      (2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N := by
    nlinarith [mul_le_mul_of_nonneg_left hwidth hδ,
      mul_le_mul_of_nonneg_left hcardR hε]
  exact hrow.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCp)
    (Real.rpow_le_rpow_of_exponent_le hZ hexp) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    (mul_nonneg hCp (pow_nonneg (le_trans zero_le_one (le_max_left 1 Cs)) _)))

/-- The density degree is chosen before the analytic parameters, hence before
τ. Source norms are supplied by actual buffered plain/slot estimates, while
all row multiplicities come from the fixed natural dictionary. -/
theorem actual_joint_high_source_energy {Base Family : Type*} [Fintype Base] [Fintype Family]
    (base : Base → Character) (B Q loss : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a E : ℝ) (i : ℕ), q ≤ Q → 33/40 ≤ a → a ≤ 7/8 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ D : NonzeroJointSourceLabel left u₀ unit → HighSourceDatum M H P η₀ Z Family,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Base,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      (∀ l ∈ labels, HighSourceAdmissible hH P η₀ Z a i n (D l)) →
      (∀ l ∈ labels, (D l).total P ≤ E ∧ (D l).liveCard P ≤ N) →
      (∀ l ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff ((D l).character j) I =
        idealCoeff (excluded (naturalRow (base (dictionary l j))
          (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (puncture l j)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ zeroMaximum (D l).character (D l).hcharacter (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      (∑ l ∈ labels, ‖(D l).row P‖^2) ≤
        C*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨J,Cd,hCd,hcount⟩ := actual_joint_buffered_high_row_count base B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cp,Cs,hCp,hCs,hrow⟩ := actual_high_source_datum M H hH P
  let K := Cp^2*(max 1 Cs)^N
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left 1 Cs)) _)
  refine ⟨n,Cd*K,mul_pos hCd hK,?_⟩
  intro η₀
  filter_upwards [hrow η₀, eventually_ge_atTop (2:ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have ha₀ : 51/100 ≤ a := by linarith
  have ha₁ : a ≤ 1 := by linarith
  have ha₂ : 1/2 ≤ a := by linarith
  have hT : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hc := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    hq ha ha' hT labels (fun l j => (D l).character j) dictionary puncture
    (fun _ _ => false) (fun l j => (D l).hcharacter j)
    hmask hzero hnonzero heq hsupport hnorm hmissing
  let xp := (2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N
  have hpoint : ∀ l ∈ labels, ‖(D l).row P‖^2 ≤ K*Z^xp := by
    intro l hl
    exact high_source_datum_cap M H P hZ.1.le hCs.le ha₂
      (hZ.2 a ha₀ ha₁ i (D l) (hvalid l hl)) (hsize l hl).1 (hsize l hl).2
  calc
    (∑ l ∈ labels, ‖(D l).row P‖^2) ≤ (labels.card:ℝ)*(K*Z^xp) := by
      simpa using Finset.sum_le_sum hpoint
    _ ≤ (Cd*(1+3*(i+1 : ℕ)*Z^P.τ)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss))*(K*Z^xp) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hK.le (Real.rpow_nonneg hZp.le _))
    _ = _ := by
      have hp : Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
          2*P.εplain*P.d+2*P.εslot*P.d*N) =
          Z^(m+q*unmarkedDensity (2*a-1)+loss)*Z^xp := by
        rw [←Real.rpow_add hZp]
        dsimp [xp]
        congr 1
        ring
      rw [hp]
      ring

#print axioms actual_joint_high_source_energy
#print axioms actual_high_source_datum
#print axioms high_source_datum_cap
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.HighSourceEnergy -/
