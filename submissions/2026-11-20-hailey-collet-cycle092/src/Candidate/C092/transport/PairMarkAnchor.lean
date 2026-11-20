/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Changing which ordinary ray carries an annular prime mark. The only added
zeros come from that fixed ray's own modulus. -/
import Candidate.C092.transport.CofactorPrimeUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalPair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison

namespace QRH.Cycle092.PairMarkAnchor
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_PairMarkAnchor_146418ee948bab21_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A single fixed base for every slot on this arm. -/
def anchoredBase (base old new : Character) : Character :=
  (base.product new).product old.inverse

theorem relative_coefficient (base old new : Character) (θ : RayQuotient.Characters M H)
    (I : Ideal O) :
    idealCoeff new I * idealCoeff (relativeCharacter M H hH (anchoredBase base old new) θ) I =
      if IsCoprime I new.modulus then
        idealCoeff old I * idealCoeff (relativeCharacter M H hH base θ) I else 0 := by
  by_cases hI : I=0
  · subst I; simp only [map_zero,zero_mul,ite_self]
  by_cases hgood : IsCoprime I new.modulus
  · rw [if_pos hgood,relativeCharacter_ideal,relativeCharacter_ideal]
    simp only [anchoredBase,idealCoeff_inverse_conj,idealCoeff_product,map_mul,starRingEnd_self_apply]
    have hn := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime new I hI hgood
    have hu : idealCoeff new I * conj (idealCoeff new I) = 1 := by
      rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hn]; norm_num
    calc
      _ = (idealCoeff new I*conj (idealCoeff new I)) *
          (idealCoeff old I*(idealCoeff (HeckeRayQuotient.character M H hH θ) I*conj (idealCoeff base I))) := by ring
      _ = _ := by rw [hu,one_mul]
  · rw [if_neg hgood]
    have hz : idealCoeff new I = 0 := not_ne_iff.mp (fun h => hgood ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff new I).mp h).2)
    rw [hz,zero_mul]

/-- Exact re-anchoring at a shared pitch. All coefficient and feature zeros
are retained, including any ideal dividing both original and new moduli. -/
theorem reanchored_slot (base old new : Character) (θ : RayQuotient.Characters M H)
    (m A z : O) (S : Finset (Ideal O)) (P t : ℝ) (W : Ideal O → ℂ) :
    normalizedSlot new m A z S (fun I => idealCoeff (relativeCharacter M H hH
      (anchoredBase base old new) θ) I*W I) t P =
    normalizedSlot old m A z (S.filter (fun I => IsCoprime I new.modulus))
      (fun I => idealCoeff (relativeCharacter M H hH base θ) I*W I) t P := by
  unfold normalizedSlot rowSlot
  rw [Finset.sum_filter]; congr 1
  apply Finset.sum_congr rfl; intro I hI
  have h := relative_coefficient M H hH base old new θ I
  by_cases hg : IsCoprime I new.modulus
  · rw [if_pos hg] at h ⊢
    linear_combination W I * idealRowHom (m^6*(A*z)) I * (I.absNorm:ℂ)^(Complex.I*t) * h
  · rw [if_neg hg] at h ⊢
    linear_combination W I * idealRowHom (m^6*(A*z)) I * (I.absNorm:ℂ)^(Complex.I*t) * h

#print axioms reanchored_slot
end
end QRH.Cycle092.PairMarkAnchor
