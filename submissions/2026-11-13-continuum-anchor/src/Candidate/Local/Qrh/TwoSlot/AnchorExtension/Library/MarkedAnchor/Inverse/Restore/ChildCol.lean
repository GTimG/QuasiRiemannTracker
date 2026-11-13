/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.ChildData

/-!
# Inverse.Restore.ChildCol — the full child column on the canonical pool

On the canonical pool `primePool F`, `F = outsideSquarefreeIdeals (reflectionExcludedPrimes q) D`,
every pool prime is coprime to the child modulus `(2592 q)` (`pool_coprime`), and every ideal in
the support of `μ · (data'.character y) · Φ(N·/Y)` with `b·Y ≤ D` is a product of pool primes
(`childCover`). Hence (**`col_eq_childPolynomial`**) the full child column is the inverse
polynomial of the child datum:

`col (childWeight ψ 1 y) (primeN p) Φ univ Y = polynomial (data'.character y) true (Φ · x^{-1/2}) Y 0 0`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff elementCoeff idealCoeff_span)
open OAI.SevenEighths.HeckeInverseAmplification (RowData NonzeroElement)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor IsBaseRayTwist)
open OAI.CanonicalRowCompletion (reflectionConductor reflectionExcludedPrimes idealRowHom)
open OAI.SevenEighths.HeckeDyadic (polynomial)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)

local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

section
variable (q D : ℕ)

/-- The canonical pool of the restoration. -/
abbrev childF : Finset (Ideal O) :=
  InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D

theorem childF_admissible : ∀ I ∈ childF q D, CanonicalQuadraticSieve.Admissible I :=
  InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (CanonicalRowCompletion.reflectionExcludedPrimes_bad q)

/-- Every excluded prime contains `2592 q`. -/
theorem excluded_le (P : Ideal O) (hP : P ∈ reflectionExcludedPrimes q) :
    childModulus q ≤ P := by
  unfold reflectionExcludedPrimes CanonicalQuadraticSieve.gcdMaskPrimes at hP
  rw [childModulus, Ideal.span_singleton_le_iff_mem]
  rcases Finset.mem_union.mp hP with h | h
  · rcases Finset.mem_insert.mp h with h | h
    · rw [h]
      exact Ideal.mem_span_singleton.mpr (lambda_dvd_reflectionConductor q)
    · rw [Finset.mem_singleton.mp h]
      exact Ideal.mem_span_singleton.mpr (two_dvd_reflectionConductor q)
  · have hd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp h)
    exact (Ideal.le_of_dvd hd) (Ideal.mem_span_singleton_self _)

/-- Every canonical pool prime is coprime to the child modulus. -/
theorem pool_coprime (hq : q ≠ 0) (i : primePool (childF q D)) : IsCoprime i.val (childModulus q) := by
  have hmax : i.val.IsMaximal := ConcretePrimeRowBridge.primePool_maximal _
    (fun I hI => (childF_admissible q D I hI).1) i
  obtain ⟨I, hIF, hiI⟩ := ConcretePrimeRowBridge.mem_primePool_iff.mp i.property
  have ho := (Finset.mem_filter.mp hIF).1
  have hI0 : I ≠ ⊥ := ConcretePrimeRowBridge.outsideIdealsUpTo_ne_bot _ D I ho
  have hdI : i.val ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hiI
  have hprime : Prime i.val := UniqueFactorizationMonoid.prime_of_normalized_factor _ hiI
  rw [childModulus]
  apply coprime_span_of_not_mem
  intro hc
  have hdc : i.val ∣ Ideal.span {reflectionConductor q} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc)
  have hc0 : Ideal.span {reflectionConductor q} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact CanonicalRowCompletion.reflectionConductor_ne_zero q hq
  obtain ⟨Q, hQ, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hc0 hprime.irreducible hdc
  have hQeq : i.val = Q := associated_iff_eq.mp hassoc
  have hS : i.val ∈ reflectionExcludedPrimes q := by
    unfold reflectionExcludedPrimes CanonicalQuadraticSieve.gcdMaskPrimes
    exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr (hQeq ▸ hQ))
  exact (ConcretePrimeRowBridge.mem_outsideIdealsUpTo.mp ho).2.2 _ hS hdI

/-- The child row character on a canonical pool prime: `ψ(π_P) · χ_P(y)`. -/
theorem childCoeff_pool (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    (u : NonzeroElement) (i : primePool (childF q D)) :
    idealCoeff ((childData q hq ψ hψ).character u) (Ideal.span {poolPrimary (childF q D) i}) =
      ψ (poolPrimary (childF q D) i) *
        finiteSquarefreeRow (fun i => Ideal.span {poolPrimary (childF q D) i}) hg {i} u.val := by
  have hspan := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i
  have hcop : IsCoprime (Ideal.span {poolPrimary (childF q D) i}) (childModulus q) := by
    rw [hspan]; exact pool_coprime q D hq i
  have h2 : (2 : O) ∉ Ideal.span {poolPrimary (childF q D) i} :=
    not_mem_of_coprime_childModulus _ hcop (two_dvd_reflectionConductor q)
  have hl : λ₀ ∉ Ideal.span {poolPrimary (childF q D) i} :=
    not_mem_of_coprime_childModulus _ hcop (lambda_dvd_reflectionConductor q)
  unfold childData
  rw [childData_prime _ u _ h2 hl]
  rw [childCharacter_prime q hq ψ hψ _ hcop]
  have hpp : CompletedGauss.primaryPrime (Ideal.span {poolPrimary (childF q D) i}) =
      poolPrimary (childF q D) i := by
    rw [hspan]; rfl
  rw [hpp, CanonicalRowCompletion.idealRowHom_prime _ _ (hg i)]
  unfold finiteSquarefreeRow
  rw [Finset.prod_singleton]

/-- The support of the child polynomial is covered by products of canonical pool primes. -/
theorem childCover (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (u : NonzeroElement) (I : Ideal O) (hI : I ≠ 0)
    (hμ : (UniqueFactorizationMonoid.moebius I : ℂ) *
      idealCoeff ((childData q hq ψ hψ).character u) I ≠ 0)
    (hN : (Ideal.absNorm I : ℝ) ≤ D) :
    ∃ A : Finset (primePool (childF q D)),
      I = ∏ i ∈ A, Ideal.span {poolPrimary (childF q D) i} := by
  have hsq : Squarefree I :=
    SevenEighths.CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero I
      (left_ne_zero_of_mul hμ)
  have hη : idealCoeff (childCharacter q hq ψ hψ) I ≠ 0 :=
    childData_coeff_ne_zero _ u I (right_ne_zero_of_mul hμ)
  have hS : ∀ P ∈ reflectionExcludedPrimes q, ¬ P ∣ I := by
    intro P hP hdvd
    have hmax : P.IsMaximal := CanonicalQuadraticSieve.gcdMaskPrimes_maximal _ ⟨P, hP⟩
    obtain ⟨J, rfl⟩ := hdvd
    apply hη
    rw [map_mul, childCharacter_zero q hq ψ hψ P (excluded_le q P hP), zero_mul]
  have hN1 : 1 ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
    omega
  have hND : Ideal.absNorm I ≤ D := by exact_mod_cast hN
  have hIF : I ∈ childF q D :=
    Finset.mem_filter.mpr ⟨ConcretePrimeRowBridge.mem_outsideIdealsUpTo.mpr ⟨hN1, hND, hS⟩, hsq⟩
  refine ⟨ConcretePrimeRowBridge.idealSupport (childF q D) I, ?_⟩
  rw [Finset.prod_congr rfl (fun i _ =>
    CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i)]
  exact (ConcretePrimeRowBridge.idealSupport_product_eq _ hIF hsq).symm

/-- **The full child column on the canonical pool is the child inverse polynomial.** -/
theorem col_eq_childPolynomial (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    (u : NonzeroElement) (Φ : ℝ → ℂ) (b Y : ℝ) (hY : 0 < Y) (hΦ : ∀ x, b < x → Φ x = 0)
    (hbY : b * Y ≤ D) :
    col (childWeight (poolPrimary (childF q D)) hg ψ 1 u.val)
        (primeN (poolPrimary (childF q D))) Φ Finset.univ Y =
      polynomial ((childData q hq ψ hψ).character u) true
        (fun x => Φ x * ((x : ℂ) ^ (-(1/2 : ℂ)))) Y 0 0 := by
  have hp : ∀ i, poolPrimary (childF q D) i ≠ 0 :=
    CanonicalQuadraticSieve.poolPrimary_ne_zero _ (childF_admissible q D)
  have hinj : Function.Injective (fun i => Ideal.span {poolPrimary (childF q D) i}) := by
    intro i j h
    have hi := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i
    have hj := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) j
    exact Subtype.ext (hi.symm.trans (h.trans hj))
  refine col_eq_polynomial (poolPrimary (childF q D)) hp hinj _ _ ?_ Φ Y hY ?_
  · intro i
    unfold childWeight
    rw [rowCoprimeMask_one, mul_one, childCoeff_pool q D hq ψ hψ hg u i]
  · intro I hI hμ hΦI
    apply childCover q D hq ψ hψ u I hI hμ
    have hle : (Ideal.absNorm I : ℝ) / Y ≤ b := by
      by_contra h
      exact hΦI (hΦ _ (lt_of_not_ge h))
    rw [div_le_iff₀ hY] at hle
    linarith

end

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.pool_coprime
#print axioms Qrh.MarkedAnchor.Inverse.Restore.col_eq_childPolynomial
