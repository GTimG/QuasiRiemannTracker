import Candidate.Cycle63.Moment.CanonicalFirstSigned
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ChildRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeScale

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstColumns CenteredMomentFixedRay
open CenteredMomentChildRows
open RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The table varies with live labels; the sixteen-character index set does not. -/
def firstPhaseTable (C D : Ideal O) (t : ActiveIndex C D → ℕ) (r : RayRing) : ℂ :=
  ∏ P, (QuadraticAllOddCRT.quadraticRaySign
    (ActualEisensteinCoordinates.residue (firstSignedPrime C D P))
    (QuadraticGaussRay.residueQuotientFour r) : ℂ)^(t P)

theorem firstPhaseTable_mk (C D : Ideal O) (t : ActiveIndex C D → ℕ) (n : O) :
    firstPhaseTable C D t (Ideal.Quotient.mk _ n) =
      ∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P) := by
  simp only [firstPhaseTable, sexticReciprocityPhase,
    QuadraticGaussRay.residueQuotientFour_mk]

theorem firstPhaseTable_norm (C D : Ideal O) (t : ActiveIndex C D → ℕ) (r : RayRing) :
    ‖firstPhaseTable C D t r‖ ≤ 1 := by
  have hsign (a b : EisensteinEPrimaryPhase.Coord) :
      ‖(QuadraticAllOddCRT.quadraticRaySign a b : ℂ)‖ ≤ 1 := by
    unfold QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  rw [firstPhaseTable, norm_prod]
  calc
    _ ≤ ∏ P : ActiveIndex C D, (1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hsign _ _)
    _ = 1 := by simp only [Finset.prod_const_one]

theorem actual_first_phase_dictionary (C D : Ideal O) (t : ActiveIndex C D → ℕ)
    (n : O) (hn : CanonicalQuadraticSieve.Supported (Ideal.span {n})) :
    (∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P)) =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D t) χ * rayCharacter χ n := by
  have hh := phase_expansion (firstPhaseTable C D t) n
  simpa only [supported_rayMask n hn, one_mul, firstPhaseTable_mk] using hh

theorem actual_first_phase_dictionary_mass (C D : Ideal O) (t : ActiveIndex C D → ℕ) :
    (∑ χ : RayCharacter, ‖phaseCoeff (firstPhaseTable C D t) χ‖) ≤ 16 := by
  simpa only [mul_one] using phaseCoeff_sum_norm_le (firstPhaseTable C D t) 1
    (fun _ => firstPhaseTable_norm C D t _)

theorem actual_first_left_fixed_dictionary (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      elementCoeff η n * leftCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D (activeExponent C D)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom ((u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_signed C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  rw [hu e n hn hnp, actual_first_phase_dictionary C D (activeExponent C D) n hn,
    idealRowHom_argument_mul, actual_first_left_holes C D n hn]
  simp only [Finset.mul_sum, Finset.sum_mul, childCharacter_primary η _ n hn hnp,
    idealRowHom_argument_mul]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem actual_first_right_fixed_dictionary (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      elementCoeff η n * rightCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter,
        phaseCoeff (firstPhaseTable C D (fun P => 6-activeExponent C D P)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom ((u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_signed C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  rw [hu e n hn hnp,
    actual_first_phase_dictionary C D (fun P => 6-activeExponent C D P) n hn,
    idealRowHom_argument_mul, actual_first_right_holes C D n hn]
  simp only [Finset.mul_sum, Finset.sum_mul, childCharacter_primary η _ n hn hnp,
    idealRowHom_argument_mul]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem first_dictionary_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm ≤
      η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  simpa only [childCharacter, primaryRayCharacter_modulus] using
    HeckePrimeScale.product_modulus_bound η (primaryRayCharacter χ)

/-- The live parent row remains a numerator. It does not become an
additional member of the fixed dictionary. -/
theorem actual_first_left_original_row (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ u₀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D (activeExponent C D)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_fixed_dictionary η C D hC
  refine ⟨u, ?_⟩
  intro u₀ e n hn hnp
  have hh := congrArg (fun x : ℂ => idealRowHom u₀ (Ideal.span {n})*x) (hu e n hn hnp)
  simp only [Finset.mul_sum, idealRowHom_argument_mul] at hh ⊢
  convert hh using 1
  · ring
  · apply Finset.sum_congr rfl
    intro χ _
    ring

theorem actual_first_right_original_row (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ u₀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter,
        phaseCoeff (firstPhaseTable C D (fun P => 6-activeExponent C D P)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_fixed_dictionary η C D hC
  refine ⟨u, ?_⟩
  intro u₀ e n hn hnp
  have hh := congrArg (fun x : ℂ => idealRowHom u₀ (Ideal.span {n})*x) (hu e n hn hnp)
  simp only [Finset.mul_sum, idealRowHom_argument_mul] at hh ⊢
  convert hh using 1
  · ring
  · apply Finset.sum_congr rfl
    intro χ _
    ring

#print axioms actual_first_phase_dictionary
#print axioms actual_first_phase_dictionary_mass
#print axioms actual_first_left_fixed_dictionary
#print axioms actual_first_right_fixed_dictionary
#print axioms first_dictionary_modulus_bound
#print axioms actual_first_left_original_row
#print axioms actual_first_right_original_row
end
end OAI.SevenEighths.Cycle63Moment
