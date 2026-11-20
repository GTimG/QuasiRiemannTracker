/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.CofactorPrimeSlot
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask

set_option autoImplicit false
namespace QRH.Cycle092.CofactorPrime
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckeInverseAmplification
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

/-- The true sixth-power cofactor creates exactly the prime deletion mask.
It leaves the power-one core and all original row/character phases intact. -/
theorem sixth_cofactor_slot (η : Character) (m A b z : O) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (t P : ℝ)
    (hprime : ∀ I∈S,Prime I) (hsupport : ∀ I∈S,Supported I) :
    normalizedSlot η m A (b^6*z) S β t P =
      normalizedSlot η m A z (puncturedPool S (Ideal.span {b})) β t P := by
  unfold normalizedSlot rowSlot puncturedPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [show m^6*(A*(b^6*z))=(m^6*(A*z))*b^6 by ring,
    idealRowHom_argument_mul,idealRowHom_sixth_mask b I (hsupport I hI)]
  have hc : IsCoprime I (Ideal.span {b}) ↔ ¬I∣Ideal.span {b} := by
    rw [isCoprime_comm]
    exact prime_coprime_iff ⟨I,hprime I hI⟩ _
  by_cases hd : I∣Ideal.span {b} <;> simp [hc,hd]

/-- Fixed holes disappear entirely once the live annulus lies beyond their
norm. Zero-width pools are deliberately not passed to this assertion. -/
theorem fixed_holes_vanish (η χ : Character) (m A z : O) (S : Finset (Ideal O))
    {B : Ideal O} (hB : B ≠ 0) (hprime : ∀ I∈S,Prime I)
    (W : ℝ→ℂ) {a b P : ℝ} (ha : 0 < a) (hP : 0 < P)
    (hWs : Function.support W ⊆ Set.Icc a b) (hlarge : (B.absNorm : ℝ) < a*P)
    (σ freq t : ℝ) :
    normalizedSlot η m A z S (slotCoefficient χ W P σ freq) t P =
      normalizedSlot η m A z (puncturedPool S B) (slotCoefficient χ W P σ freq) t P := by
  have he : activeDeleted S B W P=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro I hI
    have hm := Finset.mem_filter.mp hI
    have hn : (I.absNorm : ℝ) ≤ (B.absNorm : ℝ) := by
      exact_mod_cast Nat.le_of_dvd
        (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)) (map_dvd Ideal.absNorm hm.2.1)
    have hs := hWs hm.2.2
    have hl := (le_div_iff₀ hP).mp hs.1
    linarith
  have hd := normalizedSlot_deletion η χ m A z S B W P σ freq t
  rw [he] at hd
  simpa only [normalizedSlot,rowSlot,Finset.sum_empty,mul_zero,sub_eq_zero] using hd

/-- K.3 for the original b^6*c prime slot, rather than an arbitrary scalar
deletion error: the exact sixth-power mask and the true annular count are both
discharged. Supported prime pools are kept explicit, as in the original source. -/
theorem original_cofactor_deletion (W : ℝ→ℂ) (hW : Continuous W) {a b : ℝ}
    (ha : 0 < a) (hWs : Function.support W ⊆ Set.Icc a b) (lo hi : ℝ) :
    ∃ C : ℝ,0 < C ∧ ∀ (η χ : Character) (m A cofactor z : O)
      (S : Finset (Ideal O)) (U P exponent σ freq t : ℝ),
      (∀ I∈S,Prime I) → (∀ I∈S,Supported I) → cofactor ≠ 0 →
      0 < U → 1 < P → (a⁻¹)^2 ≤ P →
      ((Ideal.span {cofactor} : Ideal O).absNorm : ℝ) ≤ U^exponent → σ∈Set.Icc lo hi →
      ‖normalizedSlot η m A z S (slotCoefficient χ W P σ freq) t P-
        normalizedSlot η m A (cofactor^6*z) S (slotCoefficient χ W P σ freq) t P‖ ≤
        (C/Real.sqrt P)*(2*exponent*Real.log U/Real.log P) := by
  obtain ⟨C,hC,hbound⟩ := normalized_annular_deletion W hW ha hWs lo hi
  refine ⟨C,hC,?_⟩
  intro η χ m A cofactor z S U P exponent σ freq t hprime hs hc hU hP hscale hcap hσ
  rw [sixth_cofactor_slot η m A cofactor z S (slotCoefficient χ W P σ freq) t P hprime hs]
  have hc' : (Ideal.span {cofactor} : Ideal O) ≠ 0 := by
    intro h
    apply hc
    exact Ideal.span_singleton_eq_bot.mp (by simpa only [Ideal.zero_eq_bot] using h)
  exact hbound η χ m A z S (Ideal.span {cofactor}) U P exponent σ freq t
    hprime hc' hU hP hscale hcap hσ

end
end QRH.Cycle092.CofactorPrime
#print axioms QRH.Cycle092.CofactorPrime.original_cofactor_deletion
