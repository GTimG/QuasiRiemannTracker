/- The extraction of the second common part of a live LOW child pays the width reduction of its direct deletion at the
rate `κq`, up to the nonunit frequency generator, in terms of the norms of the ideals. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.LowBranch.DirectDeletionPrimes
import Candidate.Cycle63.Physical.InitialMass.LowChildRadicalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondMovingSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger CenteredMomentRankinRadical
open CenteredMomentSectorLocalization CenteredMomentPartitionNorm CenteredMomentFirstMixedRoot
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondMovingSupport CenteredMomentSupport
open CenteredMomentFirstCanonicalFamily Cycle63Moment.LowBranch

/-- The logarithm of the norm of a prime of the common support is nonnegative. -/
theorem commonPrime_log_nonneg (C D : Ideal O) (hC : Supported C) (Z : ℝ) (hZ : 1 < Z) (P : CommonIndex C D) :
    0 ≤ Real.logb Z (Ideal.absNorm P.val : ℝ) :=
  Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))

/-- The logarithm of the norm of a product of primes of the common support is the sum of their logarithms. -/
theorem logb_norm_prod_support (C D : Ideal O) (hC : Supported C) (Z : ℝ) (T : Finset (CommonIndex C D)) :
    Real.logb Z (Ideal.absNorm (∏ P ∈ T, P.val) : ℝ) = ∑ P ∈ T, Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  simp only [map_prod, Nat.cast_prod]
  exact Real.logb_prod _ _ (fun P _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))

/-- The logarithm of the norm of a product of powers of the primes of the common support. -/
theorem logb_norm_power_product (C D : Ideal O) (hC : Supported C) (Z : ℝ) (e : CommonIndex C D → ℕ) :
    Real.logb Z (Ideal.absNorm (∏ P : CommonIndex C D, P.val ^ e P) : ℝ) =
      ∑ P : CommonIndex C D, (e P : ℝ) * Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun P _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)))]
  exact Finset.sum_congr rfl (fun P _ => Real.logb_pow _ _ _)

/-- The logarithm of the norm of the first ideal is the exponent-weighted sum over the common primes. -/
theorem logb_norm_left (C D : Ideal O) (hC : Supported C) (hCD : primeSupport C = primeSupport D) (Z : ℝ) :
    Real.logb Z (C.absNorm : ℝ) =
      ∑ P : CommonIndex C D, (CenteredMomentCanonicalFirst.leftExponent C D P : ℝ) * Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  have h := left_ideal_product C D hC hCD
  simp only [commonPrime_span C D hC] at h
  conv_lhs => rw [← h]
  exact logb_norm_power_product C D hC Z _

/-- The logarithm of the norm of the second ideal is the exponent-weighted sum over the common primes. -/
theorem logb_norm_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (Z : ℝ) :
    Real.logb Z (D.absNorm : ℝ) =
      ∑ P : CommonIndex C D, (CenteredMomentCanonicalFirst.rightExponent C D P : ℝ) * Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  have h := right_ideal_product C D hC hD hCD
  simp only [commonPrime_span C D hC] at h
  conv_lhs => rw [← h]
  exact logb_norm_power_product C D hC Z _

/-- The logarithm of the norm of the common frequency generator. -/
theorem logb_normValue_commonFrequency (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z (normValue (commonFrequencyGenerator C D)) =
      ∑ P : CommonIndex C D, ((min (CenteredMomentCanonicalFirst.leftExponent C D P) (CenteredMomentCanonicalFirst.rightExponent C D P) : ℕ) : ℝ) *
        Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  have h : normValue (commonFrequencyGenerator C D) =
      (Ideal.absNorm (∏ P : CommonIndex C D, P.val ^ min (CenteredMomentCanonicalFirst.leftExponent C D P) (CenteredMomentCanonicalFirst.rightExponent C D P)) : ℝ) := by
    unfold normValue
    rw [commonFrequencyGenerator_span C D hC]
    unfold commonIdeal
    simp only [commonPrime_span C D hC]
  rw [h]
  exact logb_norm_power_product C D hC Z _

/-- The logarithm of the norm of the nonunit frequency generator. -/
theorem logb_normValue_nonunit (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) (Z : ℝ) :
    Real.logb Z (normValue (nonunitFrequencyGenerator C D U)) =
      ∑ P ∈ nonunitPartitionSet C D U, Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  have h : normValue (nonunitFrequencyGenerator C D U) =
      (Ideal.absNorm (∏ P ∈ nonunitPartitionSet C D U, P.val) : ℝ) := by
    unfold normValue
    rw [nonunitFrequencyGenerator_span C D U]
    unfold unitIdeal
    simp only [commonPrime_span C D hC]
  rw [h]
  exact logb_norm_prod_support C D hC Z _

/-- The logarithm of the norm of the common radical. -/
theorem logb_norm_commonRadical (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z ((commonRadical C D).absNorm : ℝ) =
      ∑ P : CommonIndex C D, Real.logb Z (Ideal.absNorm P.val : ℝ) := by
  have h : commonRadical C D = ∏ P : CommonIndex C D, P.val := by
    unfold commonRadical
    exact (Finset.prod_coe_sort (commonSupport C D) (fun P => P)).symm
  rw [h]
  have := logb_norm_prod_support C D hC Z Finset.univ
  exact this

/-- The common radical of two ideals with the same support has at most the width of either. -/
theorem logb_commonRadical_le (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (hE : E = C ∨ E = D) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z ((commonRadical C D).absNorm : ℝ) ≤ Real.logb Z (E.absNorm : ℝ) := by
  rw [logb_norm_commonRadical C D hC Z]
  rcases hE with rfl | rfl
  · rw [logb_norm_left E D hC hCD Z]
    refine Finset.sum_le_sum (fun P _ => ?_)
    have h1 : (1 : ℝ) ≤ CenteredMomentCanonicalFirst.leftExponent E D P := by exact_mod_cast CenteredMomentCanonicalFirst.leftExponent_pos E D P
    nlinarith [commonPrime_log_nonneg E D hC Z hZ P]
  · rw [logb_norm_right C E hC hD hCD Z]
    refine Finset.sum_le_sum (fun P _ => ?_)
    have h1 : (1 : ℝ) ≤ CenteredMomentCanonicalFirst.rightExponent C E P := by exact_mod_cast CenteredMomentCanonicalFirst.rightExponent_pos C E P
    nlinarith [commonPrime_log_nonneg C E hC Z hZ P]

/-- A sum over a finite type of nonnegative terms, restricted to a predicate that implies membership in a finite
set, is at most the sum over that set. -/
theorem sum_ite_le_of_subset {ι : Type*} [Fintype ι] (p : ι → Prop) {inst : DecidablePred p} (T : Finset ι)
    (n : ι → ℝ) (hn : ∀ i, 0 ≤ n i) (hp : ∀ i, p i → i ∈ T) :
    (∑ i, @ite ℝ (p i) (inst i) (n i) 0) ≤ ∑ i ∈ T, n i := by
  calc (∑ i, @ite ℝ (p i) (inst i) (n i) 0) ≤ ∑ i, if i ∈ T then n i else 0 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hi : p i
        · rw [ite_eq_left hi, ite_eq_left (hp i hi)]
        · rw [ite_eq_right hi]
          split_ifs
          · exact hn i
          · exact le_rfl
    _ = ∑ i ∈ T, n i := by rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The extraction of the second common part of a live child pays the width reduction `g - t` of its common
frequency generator and inactive set at the rate `κq`, up to the width of its nonunit frequency generator: `E` is
either of the two ideals of the pair, `U` its inactive set, and the pair has a nonzero correlation at its frequency. -/
theorem second_pair_prime_reserve (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (hE : E = C ∨ E = D) (U : Finset (CommonIndex C D))
    (w : O) (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D * w) ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) {κq : ℝ} (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2) :
    κq * (Real.logb Z (normValue (commonFrequencyGenerator C D)) -
        Real.logb Z (Ideal.absNorm (∏ j ∈ U, j.val) : ℝ) -
        Real.logb Z (normValue (nonunitFrequencyGenerator C D U))) ≤
      (Real.logb Z (E.absNorm : ℝ) - Real.logb Z ((commonRadical C D).absNorm : ℝ)) +
        κq * ((Real.logb Z (E.absNorm : ℝ) - Real.logb Z (normValue (commonFrequencyGenerator C D))) +
          Real.logb Z (Ideal.absNorm (∏ j ∈ U, j.val) : ℝ)) := by
  have hneq : ∀ P : CommonIndex C D, CenteredMomentCanonicalFirst.leftExponent C D P ≠ CenteredMomentCanonicalFirst.rightExponent C D P →
      6 ∣ min (CenteredMomentCanonicalFirst.leftExponent C D P) (CenteredMomentCanonicalFirst.rightExponent C D P) :=
    fun P hP => actual_unequal_min_six C D hC hD hCD w hne P hP
  have hn : ∀ P ∈ (Finset.univ : Finset (CommonIndex C D)), 0 ≤ Real.logb Z (Ideal.absNorm P.val : ℝ) :=
    fun P _ => commonPrime_log_nonneg C D hC Z hZ P
  have hG := logb_normValue_commonFrequency C D hC Z
  have hT := logb_norm_prod_support C D hC Z U
  have hV := logb_normValue_nonunit C D hC U Z
  have hR := logb_norm_commonRadical C D hC Z
  have hfilter : ∀ P : CommonIndex C D, (CenteredMomentCanonicalFirst.leftExponent C D P = 1 ∧ CenteredMomentCanonicalFirst.rightExponent C D P = 1 ∧ P ∉ U) →
      P ∈ nonunitPartitionSet C D U := by
    intro P ⟨h1, h2, h3⟩
    simp only [nonunitPartitionSet, equalActiveSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨⟨by omega, by omega⟩, h3⟩
  rcases hE with rfl | rfl
  · have h := second_prime_reserve (Finset.univ : Finset (CommonIndex E D)) U
      (CenteredMomentCanonicalFirst.leftExponent E D) (CenteredMomentCanonicalFirst.rightExponent E D)
      (fun P => Real.logb Z (Ideal.absNorm P.val : ℝ)) hκq hκq2 hn
      (fun P _ => CenteredMomentCanonicalFirst.leftExponent_pos E D P)
      (fun P _ => CenteredMomentCanonicalFirst.rightExponent_pos E D P) (Finset.subset_univ U)
      (fun P _ => hneq P)
    have hL := logb_norm_left E D hC hCD Z
    rw [hG, hT, hL, hR]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hκq) h
    rw [sub_le_sub_iff_left, hV]
    exact sum_ite_le_of_subset _ _ _ (fun P => commonPrime_log_nonneg E D hC Z hZ P) hfilter
  · have hmin : ∀ P : CommonIndex C E, min (CenteredMomentCanonicalFirst.rightExponent C E P)
        (CenteredMomentCanonicalFirst.leftExponent C E P) =
        min (CenteredMomentCanonicalFirst.leftExponent C E P) (CenteredMomentCanonicalFirst.rightExponent C E P) :=
      fun P => min_comm _ _
    have h := second_prime_reserve (Finset.univ : Finset (CommonIndex C E)) U
      (CenteredMomentCanonicalFirst.rightExponent C E) (CenteredMomentCanonicalFirst.leftExponent C E)
      (fun P => Real.logb Z (Ideal.absNorm P.val : ℝ)) hκq hκq2 hn
      (fun P _ => CenteredMomentCanonicalFirst.rightExponent_pos C E P)
      (fun P _ => CenteredMomentCanonicalFirst.leftExponent_pos C E P) (Finset.subset_univ U)
      (fun P _ hP => by rw [hmin P]; exact hneq P (Ne.symm hP))
    simp only [hmin] at h
    have hL := logb_norm_right C E hC hD hCD Z
    rw [hG, hT, hL, hR]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hκq) h
    rw [sub_le_sub_iff_left, hV]
    exact sum_ite_le_of_subset _ _ _ (fun P => commonPrime_log_nonneg C E hC Z hZ P)
      (fun P hP => hfilter P ⟨hP.2.1, hP.1, hP.2.2⟩)

/-- The active conductor of a pair of ideals with a supported first ideal is not zero. -/
theorem activeConductor_ne_zero' (C D : Ideal O) (hC : Supported C) : activeConductor C D ≠ 0 := by
  intro h
  exact (activeConductor_supported C D hC).1
    (by rw [Ideal.zero_eq_bot]; exact Ideal.span_singleton_eq_bot.mpr h)

/-- The active conductor of a pair of ideals has at most the width of its first ideal. -/
theorem logb_activeConductor_le_left (C D : Ideal O) (hC : Supported C) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (activeConductor C D)) ≤ Real.logb Z (C.absNorm : ℝ) := by
  have h : normValue (activeConductor C D) ≤ (C.absNorm : ℝ) :=
    divisor_norm_le _ C hC.1 ((activeConductor_span_dvd C D).trans (commonPart_dvd C D hC.1))
  exact Real.logb_le_logb_of_le hZ (normValue_pos _ (activeConductor_ne_zero' C D hC)) h

/-- The active conductor of a pair of ideals has at most the width of its second ideal. -/
theorem logb_activeConductor_le_right (C D : Ideal O) (hC : Supported C) (hD : Supported D) (Z : ℝ)
    (hZ : 1 < Z) : Real.logb Z (normValue (activeConductor C D)) ≤ Real.logb Z (D.absNorm : ℝ) := by
  have h : normValue (activeConductor D C) ≤ (D.absNorm : ℝ) :=
    divisor_norm_le _ D hD.1 ((activeConductor_span_dvd D C).trans (commonPart_dvd D C hD.1))
  have hswap : normValue (activeConductor D C) = normValue (activeConductor C D) := by
    unfold normValue
    rw [active_span_swap C D]
  rw [hswap] at h
  exact Real.logb_le_logb_of_le hZ (normValue_pos _ (activeConductor_ne_zero' C D hC)) h

end
end OAI.SevenEighths.Cycle63InitialMass
