/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Beyond the fixed modulus every active prime coefficient re-anchors exactly.
At shorter scales the entire original factor has bounded absolute value. -/
import Candidate.C092.transport.PairMarkHeight

namespace QRH.Cycle092.PairMarkAnchor
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification HeckePrimeAnnular HeckeDyadic CenteredMomentPrimeSlot
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.WholeSlot QRH.Cycle092.CofactorPrime
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_PairMarkAnnulus_31fb92de1e03f54f_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem full_annulus_norm (base old new : Character) (θ : RayQuotient.Characters M H)
    (m A z : O) (P σ tOld tNew v : ℝ) (hP : 0 < P) (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hlarge : (new.modulus.absNorm:ℝ)<P) :
    ‖normalizedSlot new m A z (primePool M H 2 P) (fun I => idealCoeff (relativeCharacter M H hH
      (anchoredBase base old new) θ) I*annularWeight W P σ (tOld+v-tNew) I) tNew P‖ =
    ‖normalizedSlot old m A z (primePool M H 2 P)
      (fun I => idealCoeff (relativeCharacter M H hH base θ) I*annularWeight W P σ v I) tOld P‖ := by
  let S := primePool M H 2 P
  have hp (I : Ideal O) (hi : I∈S) : Prime I := (Finset.mem_filter.mp hi).2.1
  have hfilter : S.filter (fun I => IsCoprime I new.modulus) = puncturedPool S new.modulus := by
    unfold puncturedPool; apply Finset.filter_congr
    intro I hI
    rw [isCoprime_comm]
    exact prime_coprime_iff ⟨I,hp I hI⟩ _
  have he := separate_pitch_norm M H hH base old new θ m A z S P σ tOld tNew v hP W
  rw [hfilter] at he
  have hfull := fixed_holes_vanish old (relativeCharacter M H hH base θ) m A z S new.modulus_ne_bot hp W
    (by norm_num : (0:ℝ)<1) hP hs (by simpa only [one_mul] using hlarge) σ v tOld
  exact he.trans (congrArg (fun a : ℂ => ‖a‖) hfull.symm)

theorem short_annulus_bound (W : ℝ → ℂ) (hW : Continuous W) (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (new : Character) : ∃ C : ℝ, 0 < C ∧ ∀ (old base : Character) (θ : RayQuotient.Characters M H)
      (m A z : O) (P σ v t : ℝ), 1 ≤ P → P ≤ (new.modulus.absNorm:ℝ) → 0 ≤ σ →
      ‖normalizedSlot old m A z (primePool M H 2 P)
        (fun I => idealCoeff (relativeCharacter M H hH base θ) I*annularWeight W P σ v I) t P‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := TinyCore.original_slot_coefficient_bound W hW hs
  let N := (new.modulus.absNorm:ℝ)
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr new.modulus_ne_bot)
  refine ⟨256*B*N,by positivity,?_⟩
  intro old base θ m A z P σ v t hP hPN hσ
  have hP' := zero_lt_one.trans_le hP
  have hrow := rowSlot_bound old m A z (primePool M H 2 P)
    (fun I => idealCoeff (relativeCharacter M H hH base θ) I * annularWeight W P σ v I)
    t (2*P) B (by positivity) hB.le (fun I _ => hb _ _ _ _ I hP' hσ)
    (fun I _ hI => TinyCore.original_slot_norm_cap W hs _ _ _ _ I hP' hI)
  unfold normalizedSlot
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg P)]
  have hroot : 1 ≤ Real.sqrt P := by simpa using Real.sqrt_le_sqrt hP
  calc
    _ ≤ ‖rowSlot old m A z _ _ t‖ := mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hroot)
    _ ≤ _ := hrow.trans (by change 128*B*(2*P) ≤ 256*B*N; nlinarith only [mul_le_mul_of_nonneg_left hPN hB.le])

#print axioms full_annulus_norm
#print axioms short_annulus_bound
end
end QRH.Cycle092.PairMarkAnchor
