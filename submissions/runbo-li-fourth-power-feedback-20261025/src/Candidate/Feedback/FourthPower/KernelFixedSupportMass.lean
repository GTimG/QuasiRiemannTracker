/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform finite-support Euler mass for common punctures and marked-only holes.
The subpower divisor-support theorem is imported unchanged from the baseline.
-/
import Candidate.Feedback.FourthPower.KernelRestrictedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.KernelFixedSupportMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem prime_divisors_in_support (F : Id) (hF : F ≠ 0) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P ∧ P ∣ F) : S ⊆ IdealMobiusDivisorSum.primeSupport F := by
  intro P hP
  have hp := (hS P hP).1
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff hF).mpr
  exact ⟨inferInstance,Ideal.dvd_iff_le.mp (hS P hP).2⟩

/-- This constant is uniform over the support ideal and all subsets of its primes. -/
theorem support_product_subpower (a C ε : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Id, F ≠ 0 → ∀ S : Finset Id,
      S ⊆ IdealMobiusDivisorSum.primeSupport F →
      (∏ P ∈ S, (1+C*(Ideal.absNorm P : ℝ)^(-a))) ≤ K*(Ideal.absNorm F : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound (1+C) ε
    (by positivity) hε
  refine ⟨K,hK,?_⟩
  intro F hF S hS
  have hbase : 1 ≤ 1+C := by linarith
  calc
    _ ≤ ∏ _P ∈ S, (1+C) := by
      apply Finset.prod_le_prod₀
      · intro P _
        positivity
      · intro P hP
        have hp := IdealMobiusDivisorSum.support_prime (hS hP)
        have hn : (1 : ℝ) ≤ Ideal.absNorm P := by
          have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hp⟩
          change 2 ≤ Ideal.absNorm P at hh
          exact_mod_cast (show 1 ≤ Ideal.absNorm P by omega)
        have hw := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr ha)
        nlinarith
    _ = (1+C)^S.card := Finset.prod_const _
    _ ≤ (1+C)^(IdealMobiusDivisorSum.primeSupport F).card :=
      pow_le_pow_right₀ hbase (Finset.card_le_card hS)
    _ ≤ _ := hbound F hF

/-- A polynomial bound for the fixed support costs one arbitrarily small power
of the ambient scale, with a constant chosen before the support itself. -/
theorem polynomial_support_mass (a C B ε : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B → ∀ S : Finset Id,
      (∀ P ∈ S, Prime P ∧ P ∣ F) →
      (∏ P ∈ S, (1+C*(Ideal.absNorm P : ℝ)^(-a))) ≤ K*Z^ε := by
  let δ := ε/(B+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨K,hK,hbound⟩ := support_product_subpower a C δ ha hC hδ
  refine ⟨K,hK,?_⟩
  intro Z hZ F hF hcut S hS
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have he : B*δ ≤ ε := by
    have hh : (B+1)*δ = ε := mul_div_cancel₀ ε (by linarith : B+1 ≠ 0)
    nlinarith
  calc
    _ ≤ K*(Ideal.absNorm F : ℝ)^δ := hbound F hF S (prime_divisors_in_support F hF S hS)
    _ ≤ K*(Z^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hcut hδ.le) hK.le
    _ = K*Z^(B*δ) := by rw [← Real.rpow_mul hZ0.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) hK.le

end
end Candidate.Feedback.FourthPower.KernelFixedSupportMass
