import Candidate.Cycle63.Moment.CanonicalFirstDictionary

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
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
end OAI.SevenEighths.Cycle63Moment
