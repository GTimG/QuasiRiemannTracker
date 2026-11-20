/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Color both the ordinary coefficient and the fixed base. Orthogonality
removes precisely the primes of the new fixed character's modulus. -/
import Candidate.C092.transport.FixedRayPairKeep
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentTwist CenteredMomentPrimeSlot QRH.Cycle092.CofactorPrime QRH.Cycle092.WholeSlot
namespace QRH.Cycle092.FixedRayPair
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_FixedRayPairMark_037eae52f5ff2157_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH:RayOrthogonality.globalUnits M≤H)

theorem coefficient_product (base old ω:Character) (θ:RayQuotient.Characters M H)
    (I:Ideal O) :
    idealCoeff (old.product ω) I * idealCoeff (relativeCharacter M H hH (base.product ω) θ) I =
      if IsCoprime I ω.modulus then idealCoeff old I * idealCoeff (relativeCharacter M H hH base θ) I else 0 := by
  by_cases hI:I=0
  · subst I;simp only [map_zero,zero_mul,ite_self]
  by_cases h:IsCoprime I ω.modulus
  · have hn := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime ω I hI h
    have hu : idealCoeff ω I * conj (idealCoeff ω I)=1 := by
      rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hn];norm_num
    rw [if_pos h,relativeCharacter_ideal,relativeCharacter_ideal]
    simp only [idealCoeff_inverse_conj,idealCoeff_product,map_mul,starRingEnd_self_apply]
    calc
      _ = (idealCoeff ω I*conj (idealCoeff ω I))*
        (idealCoeff old I*(idealCoeff (HeckeRayQuotient.character M H hH θ) I*conj (idealCoeff base I))) := by ring
      _ = _ := by rw [hu,one_mul]
  · have hz:idealCoeff ω I=0 := not_ne_iff.mp (fun hn=>h ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff ω I).mp hn).2)
    rw [if_neg h,idealCoeff_product];simp [hz]

theorem slot_filter (base old ω:Character) (θ:RayQuotient.Characters M H)
    (m A z:O) (S:Finset (Ideal O)) (P t:ℝ) (W:Ideal O→ℂ) :
    normalizedSlot (old.product ω) m A z S (fun I=>idealCoeff (relativeCharacter M H hH (base.product ω) θ) I*W I) t P =
    normalizedSlot old m A z (S.filter (fun I=>IsCoprime I ω.modulus))
      (fun I=>idealCoeff (relativeCharacter M H hH base θ) I*W I) t P := by
  unfold normalizedSlot rowSlot
  rw [Finset.sum_filter];congr 1
  apply Finset.sum_congr rfl;intro I hI
  have hh:=coefficient_product M H hH base old ω θ I
  by_cases h:IsCoprime I ω.modulus
  · rw [if_pos h] at hh ⊢
    linear_combination ((idealRowHom (m^6*(A*z)) I)*(W I)*((I.absNorm:ℂ)^(Complex.I*t)))*hh
  · rw [if_neg h] at hh ⊢
    linear_combination ((idealRowHom (m^6*(A*z)) I)*(W I)*((I.absNorm:ℂ)^(Complex.I*t)))*hh

theorem slot_norm (base old ω:Character) (θ:RayQuotient.Characters M H) (m A z:O)
    (P σ t tNew v:ℝ) (hp:0<P) (W:ℝ→ℂ)
    (hs:Function.support W⊆Set.Icc (1:ℝ) 2) (hc:(ω.modulus.absNorm:ℝ)<P) :
    ‖normalizedSlot (old.product ω) m A z (primePool M H 2 P)
      (fun I=>idealCoeff (relativeCharacter M H hH (base.product ω) θ) I*annularWeight W P σ (t+v-tNew) I) tNew P‖ =
    ‖normalizedSlot old m A z (primePool M H 2 P)
      (fun I=>idealCoeff (relativeCharacter M H hH base θ) I*annularWeight W P σ v I) t P‖ := by
  let S:=primePool M H 2 P
  have hprime (I:Ideal O) (hi:I∈S):Prime I:=(Finset.mem_filter.mp hi).2.1
  have hf : S.filter (fun I=>IsCoprime I ω.modulus)=puncturedPool S ω.modulus := by
    unfold puncturedPool;apply Finset.filter_congr;intro I hi
    rw [isCoprime_comm];exact prime_coprime_iff ⟨I,hprime I hi⟩ _
  change ‖normalizedSlot _ _ _ _ S _ _ _‖=‖normalizedSlot _ _ _ _ S _ _ _‖
  rw [PairMarkAnchor.at_zero_pitch _ _ _ _ _ _ _ _ tNew _ hp W,PairMarkAnchor.at_zero_pitch _ _ _ _ _ _ _ _ t _ hp W]
  rw [show tNew+(t+v-tNew)=t+v by ring,slot_filter M H hH base old ω θ _ _ _ S,hf]
  have hr:=fixed_holes_vanish old (relativeCharacter M H hH base θ) m A z S ω.modulus_ne_bot hprime W
    (by norm_num : (0:ℝ)<1) hp hs (by simpa only [one_mul] using hc) σ (t+v) 0
  rw [norm_mul,norm_mul,norm_real_imaginary_power P tNew hp,norm_real_imaginary_power P t hp,one_mul,one_mul]
  exact congrArg (fun c:ℂ=>‖c‖) hr.symm

#print axioms coefficient_product
#print axioms slot_norm
end QRH.Cycle092.FixedRayPair
