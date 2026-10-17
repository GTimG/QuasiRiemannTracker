import Candidate.Cycle63.Moment.CanonicalFirstDictionary
import Candidate.Cycle63.Density.NaturalMaskTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentChildRows CenteredMomentFixedRay
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily LocalMoment
open ProbePhysical
open RayFourExpansion CanonicalRowCompletion
open ConcretePrimeRowBridge HeckeRowClosure
local notation "O" => HeckeFamily.O

def secondFixedDictionary (η : Character) (j : RayCharacter × RayCharacter) : Character :=
  childCharacter (childCharacter η j.1) j.2

theorem second_fixed_dictionary_modulus_bound (η : Character)
    (j : RayCharacter × RayCharacter) :
    (secondFixedDictionary η j).modulus.absNorm ≤
      η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm^2 := by
  exact (first_dictionary_modulus_bound (childCharacter η j.1) j.2).trans
    (by
      calc
        _ ≤ (η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
            (Ideal.span {(12:O)}).absNorm :=
          Nat.mul_le_mul_right _ (first_dictionary_modulus_bound η j.1)
        _ = _ := by ring)

def actualMaskedRowFamily (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency) : Character :=
  excluded (naturalRow (secondFixedDictionary η j) w.val w.property).character (puncture j w)

theorem actual_masked_row_ideal (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency)
    (hp : puncture j w ≠ 0) (I : Ideal O) :
    idealCoeff (actualMaskedRowFamily η puncture j w) I =
      idealCoeff (secondFixedDictionary η j) I *
        idealRowHom ((fixedBadMask*idealGenerator (puncture j w))^6*w.val) I :=
  (naturalRow (secondFixedDictionary η j) w.val w.property).masked_ideal _ hp I

theorem actual_masked_row_element (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency)
    (hp : puncture j w ≠ 0) (n : O) :
    elementCoeff (actualMaskedRowFamily η puncture j w) n =
      rowTwist (elementHom (secondFixedDictionary η j))
        (fixedBadMask*idealGenerator (puncture j w)) 1 w.val n :=
  (naturalRow (secondFixedDictionary η j) w.val w.property).masked_element _ hp n

/-- Both finite ray expansions are fixed before the live first and second labels.
The Euler puncture is paid by deletion, rather than by a conductor bound. -/
theorem actual_signed_dictionary_density (η : Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O,
      ∀ reverse : (RayCharacter × RayCharacter) → Bool,
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ w ∈ rows, rawFrequencyNorm w ≤ H ∧
        maskedActualZeroRow (actualMaskedRowFamily η puncture) reverse a T w) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hbound⟩ := fixed_natural_dictionary_masked_raw_density
    (secondFixedDictionary η) loss hloss
  refine ⟨J,C,hC,?_⟩
  intro puncture reverse a T ha ha' hT H hH rows hrows
  apply hbound (actualMaskedRowFamily η puncture) _ reverse a T ha ha' hT H hH rows hrows
  intro j w I
  exact excludePrimes_mask _ _ (support_prime (puncture j w)) I

#print axioms second_fixed_dictionary_modulus_bound
#print axioms actual_masked_row_ideal
#print axioms actual_masked_row_element
#print axioms actual_signed_dictionary_density
end
end OAI.SevenEighths.Cycle63Moment
