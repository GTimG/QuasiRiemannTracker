/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootHoleExpansion
import Submissions.sil_density_split_20261026.Density.LeafRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask

/-! Literal prime-slot Euler-hole removal, before absolute values. -/
namespace Qrh.JointDetector.RepeatedMarks.RootHoleSlots
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots
open CenteredMomentHeckeExpansion ConcreteTraceCRT ActualEisensteinCubic CenteredMomentRowNorm CenteredMomentAbsoluteEnergy
local notation "O" => HeckeFamily.O

/-- The original common ideal hole is removed by an exact subtraction.
Shared core/root primes retain their natural zero through `rowWeight`. -/
theorem normalizedSlot_mask_eq_sub (η : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) (root : Ideal O) :
    normalizedSlot η m A z S
      (fun I => (if IsCoprime I root then (1:ℂ) else 0)*β I) t P =
      normalizedSlot η m A z S β t P-
      normalizedSlot η m A z (S.filter (fun I => ¬IsCoprime I root)) β t P := by
  unfold normalizedSlot
  rw [← mul_sub]
  congr 1
  rw [rowSlot_eq_weight, rowSlot_eq_weight, rowSlot_eq_weight, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hc : IsCoprime I root <;> simp [hc]

/-- The hole error loses one square-root length, times only the number of
eligible removed primes and the original coefficient bound. -/
theorem normalizedSlot_hole_norm (η : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t P C : ℝ) (root : Ideal O)
    (hC : 0 ≤ C) (hβ : ∀ I∈S,‖β I‖≤C) :
    ‖normalizedSlot η m A z (S.filter (fun I => ¬IsCoprime I root)) β t P‖ ≤
      ‖(Real.sqrt P:ℂ)⁻¹‖ * ((S.filter (fun I => ¬IsCoprime I root)).card:ℝ)*C := by
  unfold normalizedSlot
  rw [norm_mul, rowSlot_eq_weight]
  have hterm : ∀ I∈S.filter (fun I => ¬IsCoprime I root),
      ‖β I*rowWeight η m A z t I‖ ≤ C := by
    intro I hI
    exact (norm_mul _ _).trans_le
      ((mul_le_mul (hβ I (Finset.mem_filter.mp hI).1)
        (rowWeight_norm_le_one_all η m A z t I) (norm_nonneg _) hC).trans_eq (mul_one _))
  calc
    _ ≤ ‖(Real.sqrt P:ℂ)⁻¹‖ * ∑ I∈S.filter (fun I => ¬IsCoprime I root), C := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = _ := by simp [mul_assoc]

/-- Character exclusion is removed inside the exact natural prime slot. -/
theorem naturalSlot_excluded_eq_sub (χ : Character) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (P : ℝ) (root : Ideal O) (hr : root≠0) :
    CenteredMomentCommonMaskExpansion.naturalSlot (CenteredMomentNaturalRowSource.excluded χ root) S β P =
      CenteredMomentCommonMaskExpansion.naturalSlot χ S β P -
      CenteredMomentCommonMaskExpansion.naturalSlot χ (S.filter (fun I=>¬IsCoprime I root)) β P := by
  unfold CenteredMomentCommonMaskExpansion.naturalSlot
  rw [←mul_sub,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [CenteredMomentNaturalRowSource.excluded_ideal χ root hr]
  by_cases hc : IsCoprime I root <;> simp [hc]

/-- A natural prime-hole sum has only its removed-prime cardinality cost. -/
theorem naturalSlot_hole_norm (χ : Character) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (P C : ℝ) (root : Ideal O)
    (hP : 1≤P) (hC : 0≤C) (hβ : ∀I∈S,‖β I‖≤C) :
    ‖CenteredMomentCommonMaskExpansion.naturalSlot χ (S.filter (fun I=>¬IsCoprime I root)) β P‖ ≤
      ((S.filter (fun I=>¬IsCoprime I root)).card:ℝ)*C := by
  have hinv : (Real.sqrt P)⁻¹≤1 := by
    have hs : 1≤Real.sqrt P := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hP)
    exact inv_le_one_of_one_le₀ hs
  unfold CenteredMomentCommonMaskExpansion.naturalSlot
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsum : ‖∑I∈S.filter (fun I=>¬IsCoprime I root),idealCoeff χ I*β I‖ ≤
      ((S.filter (fun I=>¬IsCoprime I root)).card:ℝ)*C := by
    calc _ ≤ ∑I∈S.filter (fun I=>¬IsCoprime I root),‖idealCoeff χ I*β I‖ := norm_sum_le _ _
      _ ≤ ∑_I∈S.filter (fun I=>¬IsCoprime I root),C := by
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact (mul_le_mul (idealCoeff_norm_le_one χ I)
          (hβ I (Finset.mem_filter.mp hI).1) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp
  exact (mul_le_mul hinv hsum (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- A fixed conductor deletion is the same literal ideal hole in the slot. -/
theorem normalizedSlot_excluded (η : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t P : ℝ) (fixed : Ideal O) (hf : fixed≠0) :
    normalizedSlot (CenteredMomentNaturalRowSource.excluded η fixed) m A z S β t P =
      normalizedSlot η m A z S (fun I=>(if IsCoprime I fixed then (1:ℂ) else 0)*β I) t P := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight,rowSlot_eq_weight]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [rowWeight,CenteredMomentNaturalRowSource.excluded_ideal η fixed hf]
  by_cases hc : IsCoprime I fixed <;> simp [hc] <;> ring

/-- The growing sixth root is exactly a common Euler hole; all shared states
are retained in the coefficient selector. -/
theorem normalizedSlot_sixth_root (η : Character) (m A u : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (root : HeckeInverseAmplification.NonzeroIdeal) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (t P : ℝ) :
    normalizedSlot η m A (u*(ConcretePrimeRowBridge.idealGenerator root.val)^6) S β t P =
      normalizedSlot η m A u S (fun I=>(if IsCoprime I root.val then (1:ℂ) else 0)*β I) t P := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight,rowSlot_eq_weight]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hm : rowWeight η m A (u*(ConcretePrimeRowBridge.idealGenerator root.val)^6) t I =
      rowWeight η (m*ConcretePrimeRowBridge.idealGenerator root.val) A u t I := by
    change (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*(u*(ConcretePrimeRowBridge.idealGenerator root.val)^6))) I)*
        (Ideal.absNorm I:ℂ)^(Complex.I*t) =
      (idealCoeff η I*CanonicalRowCompletion.idealRowHom ((m*ConcretePrimeRowBridge.idealGenerator root.val)^6*(A*u)) I)*
        (Ideal.absNorm I:ℂ)^(Complex.I*t)
    congr 3
    ring
  rw [hm,←CenteredMomentSourceRectangleMask.rowWeight_ideal_mask η m A u t hmLam hm2 root.val I]
  ring

/-- Original growing-root slots equal cleaned slots plus the difference of
fixed and moving deleted-prime sums. In particular overlap is kept exactly. -/
theorem original_root_eq_clean (η : Character) (m A u : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (root : HeckeInverseAmplification.NonzeroIdeal) (fixed : Ideal O) (hf : fixed≠0)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t P : ℝ) :
    normalizedSlot η m A (u*(ConcretePrimeRowBridge.idealGenerator root.val)^6) S β t P =
      normalizedSlot (CenteredMomentNaturalRowSource.excluded η fixed) m A u S β t P -
        (normalizedSlot η m A u (S.filter (fun I=>¬IsCoprime I root.val)) β t P -
          normalizedSlot η m A u (S.filter (fun I=>¬IsCoprime I fixed)) β t P) := by
  rw [normalizedSlot_sixth_root η m A u hmLam hm2 root S β t P,
    normalizedSlot_excluded η m A u S β t P fixed hf,
    normalizedSlot_mask_eq_sub η m A u S β t P root.val,
    normalizedSlot_mask_eq_sub η m A u S β t P fixed]
  ring

/-- Every removed prime is a prime divisor of the same root, including all
shared core/root states. This is an exact support inclusion. -/
theorem removed_primes_subset (S : Finset (Ideal O)) (root : Ideal O)
    (hroot : root ≠ ⊥) (hprime : ∀ P∈S,Prime P) :
    S.filter (fun P => ¬IsCoprime P root) ⊆ IdealMobiusDivisorSum.primeSupport root := by
  intro P hP
  obtain ⟨hPS,hcop⟩ := Finset.mem_filter.mp hP
  have hp := hprime P hPS
  have hpi := Ideal.isPrime_of_prime hp
  haveI : P.IsMaximal := hpi.isMaximal hp.ne_zero
  have hcoat : IsCoatom P := Ideal.isMaximal_def.mp inferInstance
  have hnot : ¬Codisjoint P root := fun h => hcop (Ideal.isCoprime_iff_codisjoint.mpr h)
  have hle : root ≤ P := hcoat.not_codisjoint_iff_le.mp hnot
  apply Multiset.mem_toFinset.mpr
  exact (Ideal.mem_normalizedFactors_iff hroot).mpr ⟨hpi,hle⟩

/-- A single uniform small-power bound pays every deleted prime sum. Its
loss may be allocated after the fixed finite repeated slot type is known. -/
theorem removed_primes_card_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (root : Ideal O), root ≠ ⊥ →
      ∀ (S : Finset (Ideal O)), (∀ P∈S,Prime P) →
      ((S.filter (fun P => ¬IsCoprime P root)).card:ℝ) ≤
        C*(root.absNorm:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro root hroot S hprime
  have hs : (S.filter (fun P => ¬IsCoprime P root)).card ≤
      (IdealMobiusDivisorSum.primeSupport root).card :=
    Finset.card_le_card (removed_primes_subset S root hroot hprime)
  have hp : ((IdealMobiusDivisorSum.primeSupport root).card:ℝ) ≤
      (2:ℝ)^(IdealMobiusDivisorSum.primeSupport root).card := by
    exact_mod_cast (show (IdealMobiusDivisorSum.primeSupport root).card <
      2^(IdealMobiusDivisorSum.primeSupport root).card from Nat.lt_two_pow_self).le
  exact (by exact_mod_cast hs :
    ((S.filter (fun P => ¬IsCoprime P root)).card:ℝ) ≤
      ((IdealMobiusDivisorSum.primeSupport root).card:ℝ)).trans (hp.trans (hbound root hroot))

end
end Qrh.JointDetector.RepeatedMarks.RootHoleSlots
