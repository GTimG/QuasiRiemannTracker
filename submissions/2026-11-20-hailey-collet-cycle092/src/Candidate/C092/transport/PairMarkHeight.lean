/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An independently pitched ordinary factor can carry the same whole prime
mark. Adjust the annular frequency, retaining the exact outside phase. -/
import Candidate.C092.transport.PairMarkAnchor

namespace QRH.Cycle092.PairMarkAnchor
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckePrimeAnnular HeckeDyadic CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentTwist CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem at_zero_pitch (η χ : Character) (m A z : O) (S : Finset (Ideal O))
    (P σ t v : ℝ) (hP : 0<P) (W : ℝ→ℂ) :
    normalizedSlot η m A z S (fun I => idealCoeff χ I*annularWeight W P σ v I) t P =
      (P:ℂ)^(Complex.I*t)*normalizedSlot η m A z S (fun I => idealCoeff χ I*annularWeight W P σ (t+v) I) 0 P := by
  unfold normalizedSlot rowSlot
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro I hI
  by_cases h0 : I=0
  · subst I; simp only [map_zero,zero_mul,mul_zero]
  have hn : 0 < (I.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  have he := CenteredMomentPrimeSlotShift.norm_height_split (I.absNorm:ℝ) P σ t v hn hP
  unfold annularWeight
  simp only [Complex.ofReal_div,Complex.ofReal_natCast] at he ⊢
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  linear_combination ((Real.sqrt P:ℂ)⁻¹ * idealCoeff χ I * W ((I.absNorm:ℝ)/P) * idealCoeff η I * idealRowHom (m^6*(A*z)) I) * he

variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_PairMarkHeight_a833fed447e7569c_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem separate_pitch_norm (base old new : Character) (θ : RayQuotient.Characters M H)
    (m A z : O) (S : Finset (Ideal O)) (P σ tOld tNew v : ℝ) (hP : 0 < P) (W : ℝ → ℂ) :
    ‖normalizedSlot new m A z S (fun I => idealCoeff (relativeCharacter M H hH
      (anchoredBase base old new) θ) I*annularWeight W P σ (tOld+v-tNew) I) tNew P‖ =
    ‖normalizedSlot old m A z (S.filter (fun I => IsCoprime I new.modulus))
      (fun I => idealCoeff (relativeCharacter M H hH base θ) I*annularWeight W P σ v I) tOld P‖ := by
  rw [at_zero_pitch _ _ _ _ _ _ _ _ tNew _ hP W,at_zero_pitch _ _ _ _ _ _ _ _ tOld v hP W]
  rw [show tNew+(tOld+v-tNew)=tOld+v by ring]
  rw [reanchored_slot M H hH base old new θ m A z S P 0 (annularWeight W P σ (tOld+v))]
  rw [norm_mul,norm_mul,norm_real_imaginary_power P tNew hP,norm_real_imaginary_power P tOld hP]

#print axioms separate_pitch_norm
end
end QRH.Cycle092.PairMarkAnchor
