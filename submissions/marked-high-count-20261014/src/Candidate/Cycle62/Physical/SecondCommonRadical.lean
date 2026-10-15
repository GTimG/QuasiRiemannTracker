import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinRadical

namespace Cycle62.Physical

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths UniqueFactorizationMonoid
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentRankinRadical

local notation "O" => ActualEisensteinCubic.O

/-- Every prime in the common radical occurs in the actual extracted second
frequency, with its full minimum valuation. -/
theorem common_radical_dvd_frequency (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    commonRadical C D ∣ Ideal.span {commonFrequencyGenerator C D} := by
  have hrad : commonRadical C D = ∏ P : CommonIndex C D, P.val := by
    exact (Finset.prod_coe_sort
      (s := CenteredMomentCompleteCommon.commonSupport C D) (f := id)).symm
  rw [hrad, commonFrequencyGenerator, ← Ideal.prod_span_singleton]
  simp_rw [← Ideal.span_singleton_pow, commonPrime_span C D hC]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  have hm : 1 ≤ min (leftExponent C D P) (rightExponent C D P) :=
    le_min (leftExponent_pos C D P) (rightExponent_pos C D P)
  simpa only [pow_one] using pow_dvd_pow P.val hm

/-- The first squarefree projector has genuine divisibility provenance on both
second common ideals, so it also divides the extracted common frequency. -/
theorem first_projector_dvd_frequency (L C D : Ideal O) (hL : Squarefree L)
    (hC : CanonicalQuadraticSieve.Supported C) (hD : D ≠ 0)
    (hLC : L ∣ C) (hLD : L ∣ D) :
    L ∣ Ideal.span {commonFrequencyGenerator C D} :=
  (old_mask_dvd_commonRadical L C D hL hC.1 hD hLC hLD).trans
    (common_radical_dvd_frequency C D hC)

theorem prime_support_mono {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    IdealMobiusDivisorSum.primeSupport I ⊆ IdealMobiusDivisorSum.primeSupport J := by
  intro P hP
  have hp := IdealMobiusDivisorSum.support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  simpa only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff hJ, hp, true_and] using hd.trans hIJ

/-- Equal common supports are contained in the support of the literal row once
the actual common frequency divides that row. -/
theorem common_support_in_row (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C)
    (hCD : IdealMobiusDivisorSum.primeSupport C = IdealMobiusDivisorSum.primeSupport D)
    (w : O) (hw : w ≠ 0) (hGw : commonFrequencyGenerator C D ∣ w) :
    IdealMobiusDivisorSum.primeSupport C ⊆
      IdealMobiusDivisorSum.primeSupport (Ideal.span {w}) := by
  have hspan : Ideal.span {commonFrequencyGenerator C D} ∣ Ideal.span {w} := by
    obtain ⟨v, rfl⟩ := hGw
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact dvd_mul_right _ _
  have hs := prime_support_mono (Ideal.span_singleton_eq_bot.not.mpr hw)
    ((common_radical_dvd_frequency C D hC).trans hspan)
  rw [commonRadical_support, hCD, Finset.inter_self] at hs
  simpa only [hCD] using hs

end

end Cycle62.Physical

#print axioms Cycle62.Physical.common_radical_dvd_frequency
#print axioms Cycle62.Physical.first_projector_dvd_frequency
#print axioms Cycle62.Physical.common_support_in_row
