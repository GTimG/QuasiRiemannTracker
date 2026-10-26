import Candidate.Cycle63.Moment.PrimaryMaskTransport
import Candidate.Cycle63.Moment.CanonicalFirstNorm

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion
local notation "O" => HeckeFamily.O

theorem first_signed_prime_dvd_conductor (C D : Ideal O) (hC : Supported C)
    (P : ActiveIndex C D) : firstSignedPrime C D P ∣ activeConductor C D := by
  obtain ⟨u,hu⟩ := actual_first_conductor_unit C D hC
  rw [hu]
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (firstSignedPrime C D) (Finset.mem_univ P)) _

theorem actual_first_left_source_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff η n * coprimalityMask m n *
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (activeExponent C D)*ξ))
        ((u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp, show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu 1 (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_left_natural_parent_source_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (activeExponent C D)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_right_source_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff η n * coprimalityMask m n *
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P => 6-activeExponent C D P)*ξ))
        ((u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp, show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu 1 (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_right_natural_parent_source_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P => 6-activeExponent C D P)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem exists_actual_first_natural_pair_masks (η : Character) (u₀ : O) (hu₀ : u₀ ≠ 0)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    ∃ u₁ u₂ : Oˣ, ∃ τ₁ τ₂ : Character,
      τ₁.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} ∧
      τ₂.modulus = τ₁.modulus ∧
      ∃ h₁ : u₀*(u₁:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D ≠ 0,
      ∃ h₂ : u₀*(u₂:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D ≠ 0,
      (∀ I : Ideal O, idealCoeff τ₁ I = if IsCoprime I τ₁.modulus then
        idealCoeff (naturalRow (childCharacter η
          (firstPhaseCharacter C D hC (activeExponent C D)*ξ₁))
          (u₀*(u₁:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
            firstLeftUncancelled C D) h₁).character I else 0) ∧
      (∀ I : Ideal O, idealCoeff τ₂ I = if IsCoprime I τ₂.modulus then
        idealCoeff (naturalRow (childCharacter η
          (firstPhaseCharacter C D hC (fun P => 6-activeExponent C D P)*ξ₂))
          (u₀*(u₂:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
            firstRightUncancelled C D) h₂).character I else 0) := by
  obtain ⟨u₁,hleft⟩ := actual_first_left_natural_parent_source_mask η u₀ F₀ R m C D hC E ξ₁
  obtain ⟨u₂,hright⟩ := actual_first_right_natural_parent_source_mask η u₀ F₀ R m C D hC E ξ₂
  obtain ⟨τ₁,τ₂,hM₁,hM₂,hτ₁,hτ₂⟩ := exists_canonical_first_pair
    (excluded F₀.character R) m hm hmLam hm2 C D hC E ξ₁ ξ₂
  have he : primeSubsetGenerator (fun P : CommonIndex C D => P.val) E ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mp (subsetGenerator_supported C D hC E).1
  have hF₁ : firstLeftUncancelled C D ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    apply Ideal.absNorm_eq_zero_iff.not.mp
    exact (powered_numerator_norm_pos _ _ _
      (fun P _ => firstSignedPrime_supported C D hC P)).ne'
  have hF₂ : firstRightUncancelled C D ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    apply Ideal.absNorm_eq_zero_iff.not.mp
    exact (powered_numerator_norm_pos _ _ _
      (fun P _ => firstSignedPrime_supported C D hC P)).ne'
  have h₁ := mul_ne_zero (mul_ne_zero (mul_ne_zero hu₀ u₁.ne_zero) he) hF₁
  have h₂ := mul_ne_zero (mul_ne_zero (mul_ne_zero hu₀ u₂.ne_zero) he) hF₂
  refine ⟨u₁,u₂,τ₁,τ₂,hM₁,hM₂.trans hM₁.symm,h₁,h₂,?_,?_⟩
  · exact hleft τ₁ hM₁ hτ₁ _
  · exact hright τ₂ hM₂ hτ₂ _

#print axioms exists_actual_first_natural_pair_masks
#print axioms actual_first_right_source_mask
#print axioms actual_first_right_natural_parent_source_mask
#print axioms actual_first_left_natural_parent_source_mask
#print axioms actual_first_left_source_mask
end
end OAI.SevenEighths.Cycle63Moment
