/- Copyright (c) 2026 Sil. Apache-2.0.
Actual baseline natural prime slots, with their original annular normalization
and natural character zeros, as the labelled coefficients used in restoration.
-/
import Candidate.FourthPower.KernelCollisionMass
import Candidate.FourthPower.KernelCollisionInverse
import Candidate.FourthPower.KernelHoleCompletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelNaturalSlots
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonMaskExpansion
open OAI.SevenEighths.Record12518109GainDeletion
open KernelCollisionEnergy KernelCollisionMass KernelCollisionInverse KernelHoleCompletion
local notation "Id" => Ideal ActualEisensteinCubic.O

def slotTerm (χ : Character) (pool : Finset Id) (β : Id → ℂ) (P : ℝ) (I : Id) : ℂ :=
  if I ∈ pool then (Real.sqrt P : ℂ)⁻¹*idealCoeff χ I*β I else 0

theorem sum_slotTerm (χ : Character) (pool atoms : Finset Id) (β : Id → ℂ) (P : ℝ)
    (hs : pool ⊆ atoms) : (∑ I : atoms, slotTerm χ pool β P I.val) = naturalSlot χ pool β P := by
  rw [Finset.sum_coe_sort atoms (slotTerm χ pool β P)]
  calc
    _ = ∑ I ∈ pool, slotTerm χ pool β P I :=
      (Finset.sum_subset hs (fun I _ hn => by simp [slotTerm,hn])).symm
    _ = _ := by
      rw [naturalSlot,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hi
      simp only [slotTerm,hi,ite_true,mul_assoc]

theorem annular_half_weight (N P : ℝ) (hN : 0 < N) (hP : 0 < P) (hNP : N ≤ 2*P) :
    (Real.sqrt P)⁻¹ ≤ 2*N^(-(1/2 : ℝ)) := by
  have hs : Real.sqrt N ≤ 2*Real.sqrt P := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt hP.le]
    nlinarith
  have hi : 1/Real.sqrt P ≤ 2/Real.sqrt N :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)).mpr (by simpa using hs)
  rw [Real.rpow_neg hN.le,← Real.sqrt_eq_rpow]
  simpa only [one_div,div_eq_mul_inv,one_mul] using hi

/-- This is the actual annular coefficient; no normalization by N(I) is
silently substituted for the baseline normalization by the annular scale P. -/
theorem slotTerm_bound (χ : Character) (pool : Finset Id) (β : Id → ℂ) (P B : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B)
    (hp : ∀ I ∈ pool, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) (I : Id) :
    ‖slotTerm χ pool β P I‖ ≤ centralWeight (2*B) I := by
  by_cases hi : I ∈ pool
  · have hn : 0 < (Ideal.absNorm I : ℝ) := zero_lt_one.trans_le
      (CenteredExceptionalCount.norm_one_le (hp I hi).1.1)
    have hw := annular_half_weight (Ideal.absNorm I : ℝ) P hn hP (hp I hi).2
    rw [slotTerm,ite_eq_left hi,norm_mul,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg P)]
    calc
      _ ≤ (Real.sqrt P)⁻¹*1*B := mul_le_mul
        (mul_le_mul_of_nonneg_left (idealCoeff_norm_le_one χ I) (inv_nonneg.mpr (Real.sqrt_nonneg P)))
        (hβ I hi) (norm_nonneg _) (by positivity)
      _ ≤ (2*(Ideal.absNorm I : ℝ)^(-(1/2 : ℝ)))*B := by
        simpa using mul_le_mul_of_nonneg_right hw hB
      _ = _ := by unfold centralWeight; ring
  · simpa [slotTerm,hi] using centralWeight_nonneg (2*B) (by positivity) I

theorem slotTerm_deleted (χ : Character) (R pool : Finset Id) (β : Id → ℂ) (P : ℝ)
    (hR : ∀ I ∈ R, Prime I) (hp : ∀ I ∈ pool, Prime I) (I : Id) :
    slotTerm (χ.excludePrimes R hR) pool β P I =
      if I ∈ R then 0 else slotTerm χ pool β P I := by
  by_cases hi : I ∈ pool
  · simp only [slotTerm,hi,ite_true,deleted_prime χ R hR I (hp I hi)]
    by_cases hI : I ∈ R <;> simp [hI]
  · simp [slotTerm,hi]

variable {α : Type*} [Fintype α]

theorem natural_product_completion (χ : Character) (atoms : Finset Id)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (hs : ∀ i, pool i ⊆ atoms) :
    injectiveTuplePolynomial (fun i => fun I : atoms => slotTerm χ (pool i) (β i) (P i) I.val) =
      (∏ i, naturalSlot χ (pool i) (β i) (P i)) -
        ∑ r ∈ (Finset.univ : Finset (Setoid α)).erase ⊥,
          patternPolynomial r (fun i => fun I : atoms => slotTerm χ (pool i) (β i) (P i) I.val) := by
  rw [complete_collisions]
  have he (i : α) := sum_slotTerm χ (pool i) atoms (β i) (P i) (hs i)
  simp_rw [he]

theorem natural_hole_completion (χ : Character) (atoms : Finset Id)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (R : α → Finset Id) :
    injectiveTuplePolynomial (fun i => fun I : atoms =>
      if I.val ∈ R i then 0 else slotTerm χ (pool i) (β i) (P i) I.val) =
      injectiveTuplePolynomial (fun i => fun I : atoms => slotTerm χ (pool i) (β i) (P i) I.val) -
        ∑ L ∈ (Finset.univ : Finset (Finset α)).erase Finset.univ,
          injectiveTuplePolynomial (mixed
            (fun i => fun I : atoms => slotTerm χ (pool i) (β i) (P i) I.val)
            (fun i => fun I : atoms => I.val ∈ R i) L) := by
  have h := complete_holes (I := α) (A := atoms)
    (fun i I => slotTerm χ (pool i) (β i) (P i) I.val) (fun i I => I.val ∈ R i)
  convert h using 1
  congr 1
  funext i I
  by_cases hi : I.val ∈ R i <;> simp [KernelHoleCompletion.good,hi]

/-- The collision mass bound applies to the original baseline slots, uniformly
over the character, annuli, profiles and any retained assignment restrictions. -/
theorem natural_collision_mass (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ atoms : Finset Id,
      (∀ I ∈ atoms, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ X) →
      ∀ (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ r : Setoid α, ∀ T : Finset ({q // ¬singletonBlock r q} → atoms),
      (∑ t ∈ T, ‖∏ q : {q // ¬singletonBlock r q}, ∏ i ∈ collisionBlock r q.val,
        slotTerm χ (pool i) (β i) (P i) (t q).val‖) ≤ C*X^ε := by
  obtain ⟨C,hC,hbound⟩ := actual_collision_mass (I := α) (2*B) ε (by linarith) hε
  refine ⟨C,hC,?_⟩
  intro X hX atoms ha χ pool β P hP hp hβ r T
  exact hbound X hX atoms ha r
    (fun i I => slotTerm χ (pool i) (β i) (P i) I.val)
    (fun i I => slotTerm_bound χ (pool i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hp i) (hβ i) I.val) T

end
end Candidate.FourthPower.KernelNaturalSlots
