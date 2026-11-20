/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.CofactorPrimeMask
import Candidate.C092.transport.TinyCoreSlots

set_option autoImplicit false
namespace QRH.Cycle092.CofactorPrime
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckeInverseAmplification
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentMask
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open IdealMobiusDivisorSum CenteredMomentSourceRow CenteredMomentHeckeExpansion
open QRH.Cycle092.WholeSlot
local notation "O" => ActualEisensteinCubic.O

/-- The fixed bad-prime mask kills unsupported summands, so the exact sixth
cofactor identity holds on the entire original prime pool. -/
theorem sixth_cofactor_slot_full (η : Character) (m A b z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t P : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) (hprime : ∀ I∈S, Prime I) :
    normalizedSlot η m A (b^6*z) S β t P =
      normalizedSlot η m A z (puncturedPool S (Ideal.span {b})) β t P := by
  unfold normalizedSlot rowSlot puncturedPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hs : Supported I
  · rw [show m^6*(A*(b^6*z))=(m^6*(A*z))*b^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask b I hs]
    have hc : IsCoprime I (Ideal.span {b}) ↔ ¬ I ∣ Ideal.span {b} := by
      rw [isCoprime_comm]
      exact prime_coprime_iff ⟨I,hprime I hI⟩ _
    by_cases hd : I ∣ Ideal.span {b} <;> simp [hc,hd]
  · have hz (x : O) : β I*(idealCoeff η I*idealRowHom (m^6*(A*x)) I)*
        (I.absNorm : ℂ)^(Complex.I*t) = 0 := by
      rw [mul_assoc,show (idealCoeff η I*idealRowHom (m^6*(A*x)) I)*
          (I.absNorm : ℂ)^(Complex.I*t) = rowWeight η m A x t I from rfl,
        rowWeight_zero_of_not_supported η m A x t hmLam hm2 I hs,mul_zero]
    by_cases hd : I ∣ Ideal.span {b} <;> simp [hd,hz]

/-- An all-scale bound, including P=1, with the divisor constant fixed before
U, the cofactor, every row and the original coefficient data. -/
theorem normalized_deletion_subpower (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (U P B : ℝ), 1 ≤ U → 1 ≤ P → 0 ≤ B →
      ∀ (R : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ U^L →
      ∀ (η : Character) (m A z : O) (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t : ℝ),
      (∀ I∈S, Prime I) → (∀ I∈S, ‖β I‖ ≤ B) →
      ‖normalizedSlot η m A z S β t P-
        normalizedSlot η m A z (puncturedPool S R) β t P‖ ≤ (B*D)*U^ε := by
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε L hε hL
  refine ⟨D,hD,?_⟩
  intro U P B hU hP hB R hR hcap η m A z S β t hp hb
  have hsub : deletedPool S R ⊆ idealDivisors R := by
    intro I hI
    exact (mem_idealDivisors (by simpa only [Ideal.zero_eq_bot] using hR)).mpr
      (Finset.mem_filter.mp hI).2
  have hc0 : ((deletedPool S R).card : ℝ) ≤ ((idealDivisors R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hc : ((deletedPool S R).card : ℝ) ≤ D*U^ε :=
    hc0.trans (hdiv U hU R hR hcap)
  have hr := rowSlot_card_bound η m A z (deletedPool S R) β t B hB
    (fun I hI => hp I (Finset.mem_filter.mp hI).1)
    (fun I hI => hb I (Finset.mem_filter.mp hI).1)
  have hs : 1 ≤ Real.sqrt P := by simpa using Real.sqrt_le_sqrt hP
  have hi : (Real.sqrt P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have hn : ‖(Real.sqrt P : ℂ)⁻¹‖=(Real.sqrt P)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg P)]
  rw [normalizedSlot,normalizedSlot,←mul_sub,rowSlot_deletion,norm_mul,hn]
  calc
    _ ≤ 1*(B*((deletedPool S R).card : ℝ)) := mul_le_mul hi hr (norm_nonneg _) (by positivity)
    _ ≤ 1*(B*(D*U^ε)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hB) zero_le_one
    _ = _ := by ring

variable {Slot : Type*}
variable (rayM : Ideal O) [NeZero rayM]
local instance c092LocalInst_Candidate_C092_transport_CofactorPrimeUniform_34ead442dd7c2aa3_001 : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- Uniform original-slot error. Width zero is included explicitly: all
U^w are at least one, and no positive-width/logarithmic hypothesis is used. -/
theorem original_cofactor_subpower (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : ℝ), 1 ≤ U →
      ∀ (η η₀ : Character) (θ : Slot → RayQuotient.Characters rayM Hr)
      (w σ v : Slot → ℝ) (m A b z : O) (t : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ σ i) → goodLambda ∣ m → (2 : O) ∣ m →
      b ≠ 0 → ((Ideal.span {b} : Ideal O).absNorm : ℝ) ≤ U^L →
      ∀ i : Slot,
      ‖normalizedSlot η m A z (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀ θ W U w σ v i) t (U^(w i))-
        normalizedSlot η m A (b^6*z) (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀ θ W U w σ v i) t (U^(w i))‖ ≤ K*U^ε := by
  obtain ⟨B,hB,hcoeff⟩ := QRH.Cycle092.TinyCore.original_slot_coefficient_bound W hW hWs
  obtain ⟨D,hD,hdel⟩ := normalized_deletion_subpower ε L hε hL
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro U hU η η₀ θ w σ v m A b z t hw hσ hmLam hm2 hb hcap i
  have hp : ∀ I∈originalPools rayM Hr 2 U w i, Prime I := by
    intro I hI
    exact (Finset.mem_filter.mp hI).2.1
  rw [sixth_cofactor_slot_full η m A b z _ _ t _ hmLam hm2 hp]
  have hb' : (Ideal.span {b} : Ideal O) ≠ 0 := by
    intro hz
    exact hb (Ideal.span_singleton_eq_bot.mp (by simpa only [Ideal.zero_eq_bot] using hz))
  exact hdel U (U^(w i)) B hU (Real.one_le_rpow hU (hw i)) hB.le
    (Ideal.span {b}) hb' hcap η m A z _ _ t hp
    (fun I _ => hcoeff _ _ _ _ I (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (hσ i))

end
end QRH.Cycle092.CofactorPrime
#print axioms QRH.Cycle092.CofactorPrime.original_cofactor_subpower
