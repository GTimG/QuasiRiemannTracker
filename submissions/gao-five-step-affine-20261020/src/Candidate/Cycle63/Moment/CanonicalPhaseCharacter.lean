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
    rw [ite_eq_left isUnit_one]
    change firstPhaseTable C D t (Ideal.Quotient.mk _ 1) = 1
    simp only [firstPhaseTable_mk, sexticReciprocityPhase_one_right _
      (firstSignedPrime_supported C D hC _), one_pow, Finset.prod_const_one]
  map_mul' x y := by
    by_cases hx : IsUnit x <;> by_cases hy : IsUnit y
    · simp only [ite_eq_left hx, ite_eq_left hy, ite_eq_left (hx.mul hy), firstPhaseTable_mul]
    · have hxy : ¬IsUnit (x*y) := fun h => hy (isUnit_of_mul_isUnit_right h)
      simp only [ite_eq_left hx, ite_eq_right hy, ite_eq_right hxy, mul_zero]
    · have hxy : ¬IsUnit (x*y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp only [ite_eq_right hx, ite_eq_left hy, ite_eq_right hxy, zero_mul]
    · have hxy : ¬IsUnit (x*y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp only [ite_eq_right hx, ite_eq_right hy, ite_eq_right hxy, zero_mul]
  map_nonunit' x hx := ite_eq_right hx

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
  rw [ite_eq_left hunit, firstPhaseTable_mk]

end
end OAI.SevenEighths.Cycle63Moment
