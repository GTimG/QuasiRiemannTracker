import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinSubset
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal

namespace Cycle61.Physical

open OAI OAI.SevenEighths OAI.IdealMobiusDivisorSum

noncomputable section

local notation "O" => ActualEisensteinCubic.O

/-- Uniform in the supporting ideal and in arbitrary valuations of both ideals. -/
theorem uniform_supported_pair_count (B epsilon : ℝ) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ N : Ideal O, N ≠ 0 →
      (Ideal.absNorm N : ℝ) ≤ Z ^ B → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S, v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1 ⊆ primeSupport N ∧ primeSupport v.2 ⊆ primeSupport N) →
      (∀ v ∈ S, (Ideal.absNorm v.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.2 : ℝ) ≤ Z ^ B) →
      (S.card : ℝ) ≤ C * Z ^ epsilon := by
  let a : ℝ := epsilon / (3 * (B + 1))
  have ha : 0 < a := div_pos he (by positivity)
  obtain ⟨C, hC, hcount⟩ := CenteredMomentRankinSubset.supported_power_pair_count a a ha ha
  refine ⟨C, hC, ?_⟩
  intro Z hZ N hN0 hN S hS hs hnorm
  have hZ0 : 0 < Z := by linarith
  have hZB : 0 < Z ^ B := Real.rpow_pos_of_pos hZ0 B
  have hbound := hcount N hN0 S hS hs (Z ^ B) (Z ^ B) hZB hZB hnorm
  have hsupport := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm N)) hN ha.le
  have hexponent : B * a + B * a + B * a ≤ epsilon := by
    have hid : a * (3 * (B + 1)) = epsilon := by dsimp only [a]; field_simp
    nlinarith
  calc
    (S.card : ℝ) ≤ C * (Z ^ B) ^ a * (Z ^ B) ^ a * (Ideal.absNorm N : ℝ) ^ a := hbound
    _ ≤ C * (Z ^ B) ^ a * (Z ^ B) ^ a * (Z ^ B) ^ a :=
      mul_le_mul_of_nonneg_left hsupport (by positivity)
    _ = C * Z ^ (B * a + B * a + B * a) := by
      rw [← Real.rpow_mul hZ0.le]
      rw [Real.rpow_add hZ0, Real.rpow_add hZ0]
      ring
    _ ≤ C * Z ^ epsilon := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hexponent) hC.le

/-- The equal-support interface used by the joint common-ideal fibres. -/
theorem uniform_common_pair_count (B epsilon : ℝ) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ N : Ideal O, N ≠ 0 →
      (Ideal.absNorm N : ℝ) ≤ Z ^ B → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S, v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S, primeSupport v.1 = primeSupport v.2) →
      (∀ v ∈ S, primeSupport v.1 ⊆ primeSupport N) →
      (∀ v ∈ S, (Ideal.absNorm v.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.2 : ℝ) ≤ Z ^ B) →
      (S.card : ℝ) ≤ C * Z ^ epsilon := by
  obtain ⟨C, hC, hcount⟩ := uniform_supported_pair_count B epsilon hB he
  refine ⟨C, hC, ?_⟩
  intro Z hZ N hN0 hN S hS heq hs hnorm
  apply hcount Z hZ N hN0 hN S hS _ hnorm
  intro v hv
  refine ⟨hs v hv, ?_⟩
  rw [← heq v hv]
  exact hs v hv

/-- The missing-radical count needs only nonzero ideals and a norm upper bound. -/
theorem missing_radical_card (S : Finset (Ideal O)) (Z m : ℝ) (hZ : 0 ≤ Z)
    (hS : ∀ I ∈ S, I ≠ 0) (hnorm : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ m) :
    (S.card : ℝ) ≤ 128 * Z ^ m := by
  have hb := CenteredMomentSecondDiagonal.divisible_ideal_card S (1 : Ideal O)
    (by simp) hS (fun I _ => one_dvd I) (Z ^ m) (Real.rpow_nonneg hZ m) hnorm
  simpa using hb

end

end Cycle61.Physical

#print axioms Cycle61.Physical.uniform_supported_pair_count
#print axioms Cycle61.Physical.uniform_common_pair_count
#print axioms Cycle61.Physical.missing_radical_card
