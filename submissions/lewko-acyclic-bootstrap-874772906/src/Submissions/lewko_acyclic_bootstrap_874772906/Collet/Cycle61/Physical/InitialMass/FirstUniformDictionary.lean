import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.FixedPairMasks
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.CanonicalFirstNorm

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion
open Cycle61Moment
open CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O

theorem uniform_first_left_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (u₀ e n : O), Supported (Ideal.span {n}) →
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
  intro ξ u₀ e n hn hnp
  rw [hu e n hn hnp, ← actual_first_phase_character C D hC (activeExponent C D) n hn,
    idealRowHom_argument_mul, actual_first_left_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

theorem uniform_first_right_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (u₀ e n : O), Supported (Ideal.span {n}) →
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
  intro ξ u₀ e n hn hnp
  rw [hu e n hn hnp,
    ← actual_first_phase_character C D hC (fun P => 6-activeExponent C D P) n hn,
    idealRowHom_argument_mul, actual_first_right_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

theorem uniform_first_left_natural_parent_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (χ : Character),
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
  obtain ⟨u,hu⟩ := uniform_first_left_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
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
  have hh := hu ξ u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem uniform_first_right_natural_parent_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (χ : Character),
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
  obtain ⟨u,hu⟩ := uniform_first_right_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
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
  have hh := hu ξ u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_left_single_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_left_natural_parent_mask
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_right_single_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_right_natural_parent_mask
