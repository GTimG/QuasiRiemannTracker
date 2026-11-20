/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed presentation selected by the actual witness retains the entire
original mark, including primes killed by either fixed character. -/
import Candidate.C092.transport.WitnessPrimeTwist

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckePrimeAnnular
open HeckeInverseAmplification CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots
open CenteredMomentNaturalFixedRaySource CenteredMomentTwist CanonicalRowCompletion
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_WitnessOriginalMark_e4ead13024ed5447_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem same_mark_zero_pitch (η base : Character) (j) (θ : RayQuotient.Characters M H) (m A z : O)
    (S : Finset (Ideal O)) (W : Ideal O→ℂ) (P : ℝ) :
    normalizedSlot (witnessBase M H hH η base j) m A z S (fun I => idealCoeff
      (relativeCharacter M H hH (witnessBase M H hH base base j) θ) I * W I) 0 P =
    normalizedSlot η m A z S (fun I => idealCoeff (relativeCharacter M H hH base θ) I * W I) 0 P := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl; intro I _
  have h := witness_mark_coeff M H hH η base j θ I
  linear_combination W I * idealRowHom (m^6*(A*z)) I * (I.absNorm:ℂ)^(Complex.I*(0:ℝ)) * h

/-- Every slot and either independent ordinary height, without a lower
width floor, smooth replacement of holes, or loss in the prime amplitude. -/
theorem witness_original_mark_norm (η base : Character) (j) (θ : RayQuotient.Characters M H) (m A z : O)
    (S : Finset (Ideal O)) (W : ℝ→ℂ) (P σ t t' v : ℝ) (hP : 0 < P) :
    ‖normalizedSlot (witnessBase M H hH η base j) m A z S (fun I => idealCoeff
      (relativeCharacter M H hH (witnessBase M H hH base base j) θ) I * annularWeight W P σ (t+v-t') I) t' P‖ =
    ‖normalizedSlot η m A z S (fun I => idealCoeff (relativeCharacter M H hH base θ) I * annularWeight W P σ v I) t P‖ := by
  rw [PairMarkAnchor.at_zero_pitch _ _ _ _ _ _ _ _ t' _ hP W,PairMarkAnchor.at_zero_pitch _ _ _ _ _ _ _ _ t v hP W]
  rw [show t'+(t+v-t')=t+v by ring,same_mark_zero_pitch M H hH η base j θ m A z S (annularWeight W P σ (t+v)) P]
  rw [norm_mul,norm_mul,norm_real_imaginary_power P t' hP,norm_real_imaginary_power P t hP]

#print axioms witness_original_mark_norm
end QRH.Cycle092.MediumReplace.Source
