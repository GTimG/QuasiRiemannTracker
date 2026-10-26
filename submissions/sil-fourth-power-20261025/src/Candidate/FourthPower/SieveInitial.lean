/- Copyright (c) 2026 Sil. Apache-2.0.
Initial character-sum control for repeated-prime sextic columns. Reuses
the baseline's general Polya--Vinogradov theorem, not its squarefree sieve.
The common-divisor mask is retained explicitly. -/
import Candidate.FourthPower.SieveGcd
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound

set_option autoImplicit false
namespace Candidate.FourthPower.SieveInitial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open SexticSieve SievePrimitive SieveCoupling SievePairPoisson
open QuadraticInitialBound UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem primeIndex_nonempty (I : Id) (hI : I ≠ 0) (hI1 : I ≠ 1) : Nonempty (PrimeIndex I) := by
  apply Finset.Nonempty.to_subtype
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  apply hI1
  simpa only [Ideal.one_eq_top] using (IdealMobiusDivisorSum.primeSupport_empty_iff I hI).mp he

theorem pair_nonempty (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hne : I ≠ 1 ∨ J ≠ 1) : Nonempty (PrimeIndex I ⊕ PrimeIndex J) := by
  rcases hne with h | h
  · obtain ⟨P⟩ := primeIndex_nonempty I hI.1 h
    exact ⟨Sum.inl P⟩
  · obtain ⟨P⟩ := primeIndex_nonempty J hJ.1 h
    exact ⟨Sum.inr P⟩

theorem pairModulus_norm (I J : Id) :
    ‖eisEmbedding (finitePrimeModulus (primes I J))‖ = ‖eisEmbedding (modulus I * modulus J)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [eisEmbedding_norm_sq_eq_absNorm_span, eisEmbedding_norm_sq_eq_absNorm_span,
    span_finitePrimeModulus, product_modulus]

theorem coprime_polya_vinogradov (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (hne : I ≠ 1 ∨ J ≠ 1) (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    ‖∑' z : O, (idealRowHom z I * star (idealRowHom z J)) * W (‖eisEmbedding z‖^2/A)‖ ≤
      pvControl W * ‖eisEmbedding (modulus I * modulus J)‖ := by
  let : Nonempty (PrimeIndex I ⊕ PrimeIndex J) := pair_nonempty I J hI hJ hne
  have h := canonical_polya_vinogradov (primes I J) (primes_coprime I J hI hJ hcop)
    (primes_good I J hI hJ) (primes_odd I J hI hJ) (exponents I J)
    (fun P => (exponents_range I J hI hJ hfI hfJ P).1)
    (fun P => (exponents_range I J hI hJ hfI hfJ P).2) W A hA
  simp_rw [row_identity I J hI hJ hfI hfJ, pairModulus_norm] at h
  exact h

theorem common_mask_primes (D : Id) (hD : Supported D) (z : O) :
    (if IsCoprime D (Ideal.span {z}) then (1 : ℂ) else 0) =
      rowCoprimeMask (fun P : PrimeIndex D => P.val) Finset.univ z := by
  have he : IsCoprime D (Ideal.span {z}) ↔ ∀ P ∈ normalizedFactors D, z ∉ P := by
    have hprod (s : Multiset Id) (hs : ∀ P ∈ s, P.IsMaximal) :
        IsCoprime s.prod (Ideal.span {z}) ↔ ∀ P ∈ s, z ∉ P := by
      induction s using Multiset.induction_on with
      | empty => simp only [Multiset.prod_zero, isCoprime_one_left, Multiset.notMem_zero,
          false_implies, implies_true]
      | @cons P s ih =>
        let : P.IsMaximal := hs P (Multiset.mem_cons_self _ _)
        rw [Multiset.prod_cons, IsCoprime.mul_left_iff,
          SixthPowerAverage.prime_coprime_span_iff,
          ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))]
        simp only [Multiset.mem_cons, forall_eq_or_imp]
    simpa only [Ideal.prod_normalizedFactors_eq_self hD.1] using
      hprod (normalizedFactors D) (fun P hP => (supported_factors_good D hD P hP).1)
  have hbad : (∃ P : PrimeIndex D, P ∈ Finset.univ ∧ z ∈ P.val) ↔
      ¬ IsCoprime D (Ideal.span {z}) := by
    rw [he]
    simp only [Finset.mem_univ, true_and, not_forall, not_not]
    constructor
    · rintro ⟨P,hz⟩
      exact ⟨P.val, Multiset.mem_toFinset.mp P.property, hz⟩
    · rintro ⟨P,hP,hz⟩
      exact ⟨⟨P,Multiset.mem_toFinset.mpr hP⟩,hz⟩
  simp only [rowCoprimeMask, hbad]
  split_ifs <;> rfl

theorem masked_coprime_polya_vinogradov (D I J : Id)
    (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (hne : I ≠ 1 ∨ J ≠ 1) (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    ‖∑' z : O, (if IsCoprime D (Ideal.span {z}) then (1 : ℂ) else 0) *
      (idealRowHom z I * star (idealRowHom z J)) * W (‖eisEmbedding z‖^2/A)‖ ≤
      (2 : ℝ)^(Fintype.card (PrimeIndex D)) *
        (pvControl W * ‖eisEmbedding (modulus I * modulus J)‖) := by
  let : Nonempty (PrimeIndex I ⊕ PrimeIndex J) := pair_nonempty I J hI hJ hne
  have h := canonical_masked_polya_vinogradov (fun P : PrimeIndex D => P.val)
    Subtype.val_injective Finset.univ (primes I J) (primes_coprime I J hI hJ hcop)
    (primes_good I J hI hJ) (primes_odd I J hI hJ) (exponents I J)
    (fun P => (exponents_range I J hI hJ hfI hfJ P).1)
    (fun P => (exponents_range I J hI hJ hfI hfJ P).2) W A hA
  simp_rw [row_identity I J hI hJ hfI hfJ, pairModulus_norm, ← common_mask_primes D hD] at h
  simpa only [Finset.card_univ] using h

theorem radical_norm_le (I : Id) (hI : I ≠ 0) :
    (Ideal.absNorm I.radical : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (Ideal.absNorm_dvd_absNorm_of_le I.le_radical)

theorem mask_cost_le_norm (D : Id) (hD : D ≠ 0) :
    (2 : ℝ)^Fintype.card (PrimeIndex D) ≤ Ideal.absNorm D := by
  have h := two_pow_card_le_supportNorm (fun P : PrimeIndex D => P.val) Finset.univ
  simp only [Finset.card_univ, supportNorm, radical_product D hD] at h
  exact h.trans (radical_norm_le D hD)

theorem masked_conductor_bound (D I J : Id)
    (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (B : ℝ) (hB : 0 ≤ B) (hDI : (Ideal.absNorm (D*I) : ℝ) ≤ B)
    (hDJ : (Ideal.absNorm (D*J) : ℝ) ≤ B) :
    (2 : ℝ)^Fintype.card (PrimeIndex D) * ‖eisEmbedding (modulus I * modulus J)‖ ≤ B := by
  let q := ‖eisEmbedding (modulus I * modulus J)‖
  have hq : q^2 ≤ (Ideal.absNorm I : ℝ) * Ideal.absNorm J := by
    dsimp only [q]
    rw [eisEmbedding_norm_sq_eq_absNorm_span, ← Ideal.span_singleton_mul_span_singleton,
      span_modulus I hI.1, span_modulus J hJ.1, map_mul, Nat.cast_mul]
    exact mul_le_mul (radical_norm_le I hI.1) (radical_norm_le J hJ.1) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp : q^2 * (Ideal.absNorm D : ℝ)^2 ≤ B^2 := by
    calc
      _ ≤ ((Ideal.absNorm I : ℝ)*Ideal.absNorm J)*(Ideal.absNorm D : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
      _ = (Ideal.absNorm (D*I) : ℝ) * Ideal.absNorm (D*J) := by
        simp only [map_mul, Nat.cast_mul]
        ring
      _ ≤ B*B := mul_le_mul hDI hDJ (Nat.cast_nonneg _) hB
      _ = B^2 := by ring
  have hmain : (Ideal.absNorm D : ℝ)*q ≤ B := by
    apply (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hB).mp
    nlinarith only [hp]
  exact (mul_le_mul_of_nonneg_right (mask_cost_le_norm D hD.1) (norm_nonneg _)).trans hmain

theorem masked_coprime_bound (D I J : Id)
    (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (hne : I ≠ 1 ∨ J ≠ 1) (B : ℝ) (hB : 0 ≤ B)
    (hDI : (Ideal.absNorm (D*I) : ℝ) ≤ B) (hDJ : (Ideal.absNorm (D*J) : ℝ) ≤ B)
    (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    ‖∑' z : O, (if IsCoprime D (Ideal.span {z}) then (1 : ℂ) else 0) *
      (idealRowHom z I * star (idealRowHom z J)) * W (‖eisEmbedding z‖^2/A)‖ ≤ pvControl W * B := by
  apply (masked_coprime_polya_vinogradov D I J hD hI hJ hfI hfJ hcop hne W A hA).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (masked_conductor_bound D I J hD hI hJ B hB hDI hDJ)
    (pvControl_nonneg W)

theorem powerFree_dvd {n : ℕ} {I D : Id} (hI : PowerFree n I) (hD : D ∣ I) :
    PowerFree n D := fun P hP hd => hI P hP (hd.trans hD)

/-- Uniform off-diagonal Gram bound for distinct sixth-power-free ideals.
Their radicals need not be distinct, and shared prime factors are allowed. -/
theorem gram_offdiagonal (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hne : I ≠ J)
    (B : ℝ) (hB : 0 ≤ B) (hIB : (Ideal.absNorm I : ℝ) ≤ B) (hJB : (Ideal.absNorm J : ℝ) ≤ B)
    (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    ‖∑' z : O, (idealRowHom z I * star (idealRowHom z J)) * W (‖eisEmbedding z‖^2/A)‖ ≤
      pvControl W * B := by
  let D := gcd I J
  let U := idealQuotient D I
  let V := idealQuotient D J
  have hdI : D ∣ I := gcd_dvd_left I J
  have hdJ : D ∣ J := gcd_dvd_right I J
  have hDU : D*U = I := idealQuotient_mul hdI
  have hDV : D*V = J := idealQuotient_mul hdJ
  have hD : Supported D := SixthDecomposition.supported_dvd hI hdI
  have hUd : U ∣ I := idealQuotient_dvd hdI
  have hVd : V ∣ J := idealQuotient_dvd hdJ
  have hU : Supported U := SixthDecomposition.supported_dvd hI hUd
  have hV : Supported V := SixthDecomposition.supported_dvd hJ hVd
  have hfU : PowerFree 6 U := powerFree_dvd hfI hUd
  have hfV : PowerFree 6 V := powerFree_dvd hfJ hVd
  have hcop : IsCoprime U V := (gcd_eq_iff_quotient_coprime D I J hD.1 hdI hdJ).mp rfl
  have hnon : U ≠ 1 ∨ V ≠ 1 := by
    by_contra! he
    have hi : D = I := by simpa only [he.1, mul_one] using hDU
    have hj : D = J := by simpa only [he.2, mul_one] using hDV
    exact hne (hi.symm.trans hj)
  have hterm (z : O) : idealRowHom z I * star (idealRowHom z J) =
      (if IsCoprime D (Ideal.span {z}) then (1 : ℂ) else 0) *
        (idealRowHom z U * star (idealRowHom z V)) := by
    have hm : star (idealRowHom z D) * idealRowHom z D =
        (if IsCoprime D (Ideal.span {z}) then (1 : ℂ) else 0) := SieveGcd.common_mask D hD z
    rw [← hDU, ← hDV, map_mul, map_mul, star_mul, ← hm]
    ring
  simp_rw [hterm]
  apply masked_coprime_bound D U V hD hU hV hfU hfV hcop hnon B hB _ _ W A hA
  · simpa only [hDU] using hIB
  · simpa only [hDV] using hJB

end
end Candidate.FourthPower.SieveInitial
