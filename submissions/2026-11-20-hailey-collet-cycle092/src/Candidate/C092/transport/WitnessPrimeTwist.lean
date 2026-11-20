/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The detector's fixed twists use only moduli already present in the original
mark. Retwisting the ordinary and relative base together gives exact equality
even at the bounded primes. -/
import Candidate.C092.transport.FixedWitnessLabel
import Candidate.C092.transport.PairMarkHeight

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeRowClosure CanonicalRowCompletion
open HeckeDyadic HeckeInverseAmplification CenteredMomentFixedRayInducingTransport CenteredExceptionalProfile
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_WitnessPrimeTwist_23f1ca4bf5aa1d85_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem simultaneous_twist (old base ψ : Character) (θ : RayQuotient.Characters M H)
    (hψ : (relativeCharacter M H hH base θ).modulus ≤ ψ.modulus) (I : Ideal O) :
    idealCoeff (old.product ψ) I * idealCoeff (relativeCharacter M H hH (base.product ψ) θ) I =
      idealCoeff old I * idealCoeff (relativeCharacter M H hH base θ) I := by
  have hex : idealCoeff (old.product ψ) I * idealCoeff (relativeCharacter M H hH (base.product ψ) θ) I =
      (idealCoeff ψ I * conj (idealCoeff ψ I)) *
        (idealCoeff old I * idealCoeff (relativeCharacter M H hH base θ) I) := by
    simp only [relativeCharacter_ideal,idealCoeff_inverse_conj,idealCoeff_product,map_mul]
    ring
  rw [hex]
  by_cases hn : idealCoeff (relativeCharacter M H hH base θ) I = 0
  · rw [hn,mul_zero,mul_zero]
  have hc := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff _ _).mp hn
  have hcop : IsCoprime I ψ.modulus := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact top_unique ((Ideal.isCoprime_iff_sup_eq.mp hc.2).ge.trans (sup_le_sup_left hψ _))
  have hm := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime ψ I hc.1 hcop
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hm]; norm_num

theorem witness_mark_coeff (old base : Character) (j) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (witnessBase M H hH old base j) I *
      idealCoeff (relativeCharacter M H hH (witnessBase M H hH base base j) θ) I =
      idealCoeff old I * idealCoeff (relativeCharacter M H hH base θ) I := by
  cases j with
  | none => rfl
  | some pair =>
    let ψ := (relativeCharacter M H hH base pair.1).inverse.inverse
    let ξ := HeckeRayQuotient.character M H hH pair.2
    have h₁ : (relativeCharacter M H hH base θ).modulus ≤ ψ.modulus := le_rfl
    have h₂ : (relativeCharacter M H hH (base.product ψ) θ).modulus ≤ ξ.modulus := inf_le_left
    exact (simultaneous_twist M H hH (old.product ψ) (base.product ψ) ξ θ h₂ I).trans
      (simultaneous_twist M H hH old base ψ θ h₁ I)

theorem witness_internalQ (Q : Ideal O) (hQM : Q ≤ M) (base : Character) (j) :
    internalQ Q (witnessBase M H hH base base j) = internalQ Q base := by
  cases j with
  | none => rfl
  | some pair =>
    change Q ⊓ ((base.modulus ⊓ (M ⊓ base.modulus)) ⊓ M) = Q ⊓ base.modulus
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · have hM : Q ⊓ base.modulus ≤ M := inf_le_left.trans hQM
      exact le_inf inf_le_left (le_inf (le_inf inf_le_right (le_inf hM inf_le_right)) hM)

theorem witness_initialKeep (Q : Ideal O) (hQM : Q ≤ M) (old base : Character)
    (j) (u : FreeRow) :
    initialKeep (witnessBase M H hH old base j) (internalQ Q (witnessBase M H hH base base j)) u.val ↔
      initialKeep old (internalQ Q base) u.val := by
  rw [witness_internalQ M H hH Q hQM base j]
  cases j with
  | none => rfl
  | some pair =>
    let ψ := (relativeCharacter M H hH base pair.1).inverse.inverse
    let ξ := HeckeRayQuotient.character M H hH pair.2
    let m := fixedBadMask*idealGenerator 1
    have hM : internalQ Q base ≤ M := inf_le_left.trans hQM
    have hψ : internalQ Q base ≤ ψ.modulus := le_inf hM inf_le_right
    have hξ : internalQ Q base ≤ ξ.modulus := hM
    have hm : m ≠ 0 := mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero)
    have hl : goodLambda ∣ m := (dvd_mul_right _ _ : goodLambda ∣ fixedBadMask).trans (dvd_mul_right _ _)
    have htwo : (2:O) ∣ m := (dvd_mul_left _ _ : (2:O) ∣ fixedBadMask).trans (dvd_mul_right _ _)
    change (_ ∧ ¬FixedInducingRow ((old.product ψ).product ξ) (internalQ Q base) m 1 u.val) ↔ _
    rw [fixedInducingRow_product_iff _ _ _ _ _ _ hξ hm one_ne_zero u.property.1 hl htwo,
        fixedInducingRow_product_iff _ _ _ _ _ _ hψ hm one_ne_zero u.property.1 hl htwo]
    rfl

#print axioms witness_mark_coeff
#print axioms witness_initialKeep
end QRH.Cycle092.MediumReplace.Source
