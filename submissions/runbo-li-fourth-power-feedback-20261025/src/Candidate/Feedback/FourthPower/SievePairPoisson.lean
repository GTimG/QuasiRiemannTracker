/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from the OpenAI baseline CubicSieve.PairPrimes and PairPoisson:
replace fixed cubic exponents 4/2 by the actual multiplicities e and 6-e.
The resulting Gauss phase is the coupled phase, not the cubic separated one. -/
import Candidate.Feedback.FourthPower.SieveRayCoupling

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SievePairPoisson
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open SexticSieve SievePrimitive SieveCoupling SieveGaussPairs
open EisensteinSchwartzPoisson GaussGeneratorTransport
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def primes (I J : Id) : PrimeIndex I ⊕ PrimeIndex J → Id := Sum.elim Subtype.val Subtype.val

instance primes_maximal (I J : Id) (P : PrimeIndex I ⊕ PrimeIndex J) : (primes I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

theorem primes_good (I J : Id) (hI : Supported I) (hJ : Supported J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : goodLambda ∉ primes I J P := by
  cases P with
  | inl P => exact good I hI P
  | inr P => exact good J hJ P

theorem primes_odd (I J : Id) (hI : Supported I) (hJ : Supported J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : ringChar (O ⧸ primes I J P) ≠ 2 := by
  cases P with
  | inl P => exact odd_residue I hI P
  | inr P => exact odd_residue J hJ P

theorem primes_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (primes I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I hI.1 P) (primeIndex_le J hJ.1 Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q => exact primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q => exact primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

def exponents (I J : Id) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (exponent I) (fun P => 6-exponent J P)

theorem exponents_range (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (P : PrimeIndex I ⊕ PrimeIndex J) :
    exponents I J P ≠ 0 ∧ exponents I J P < 6 := by
  cases P with
  | inl P => exact ⟨(exponent_pos I P).ne', exponent_lt I hI hfI P⟩
  | inr P =>
    have hp := exponent_pos J P
    have ht := exponent_lt J hJ hfJ P
    dsimp [exponents]
    omega

theorem inverse_local (I : Id) (hI : Supported I) (hfI : PowerFree 6 I) (P : PrimeIndex I) :
    actualSextic P.val (good I hI P)^(6-exponent I P) =
      (actualSextic P.val (good I hI P)^exponent I P)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel (exponent_lt I hI hfI P).le]
  exact actualSextic_sixth_one P.val (good I hI P)

theorem row_identity (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (z : O) :
    finiteSexticRow (primes I J) (primes_good I J hI hJ) (exponents I J) z =
      idealRowHom z I * star (idealRowHom z J) := by
  have hinv : finiteSexticRow (fun P : PrimeIndex J => P.val) (good J hJ)
      (fun P => 6-exponent J P) z =
      star (finiteSexticRow (fun P : PrimeIndex J => P.val) (good J hJ) (exponent J) z) := by
    unfold finiteSexticRow
    rw [star_prod]
    apply Finset.prod_congr rfl
    intro P _
    let : Finite (O ⧸ P.val) := inferInstance
    change (actualSextic P.val (good J hJ P)^(6-exponent J P)) (Ideal.Quotient.mk _ z) = _
    rw [inverse_local J hJ hfJ P, ← MulChar.star_apply']
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (good I hI) (exponent I) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (good J hJ) (fun P => 6-exponent J P) z = _
  rw [hinv, finite_row I hI hfI, finite_row J hJ hfJ]

theorem product_modulus (I J : Id) :
    Ideal.span {modulus I * modulus J} = ∏ P, primes I J P := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  dsimp only [modulus]
  rw [span_finitePrimeModulus, span_finitePrimeModulus, Fintype.prod_sum_type]
  rfl

def principalRow (I J : Id) (hI : Supported I) (hJ : Supported J) (hcop : IsCoprime I J) :
    O ⧸ Ideal.span {modulus I * modulus J} → ℂ :=
  principalSexticRow (primes I J) (primes_coprime I J hI hJ hcop)
    (primes_good I J hI hJ) (exponents I J) (modulus I * modulus J) (product_modulus I J)

theorem principalRow_mk (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J) (z : O) :
    principalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) =
      idealRowHom z I * star (idealRowHom z J) := by
  exact (principalSexticRow_mk _ (primes_coprime I J hI hJ hcop)
    (primes_good I J hI hJ) (exponents I J) _ (product_modulus I J) z).trans
      (row_identity I J hI hJ hfI hfJ z)

theorem principalGauss_eq (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J) :
    principalNormalizedGauss (primes I J) (primes_coprime I J hI hJ hcop)
      (primes_good I J hI hJ) (exponents I J) (modulus I * modulus J) (product_modulus I J)
      (mul_ne_zero (modulus_ne_zero I) (modulus_ne_zero J)) = pairGauss I J hI hJ := by
  let a := modulus I
  let b := modulus J
  let : Finite (O ⧸ Ideal.span {a*b}) := finite_quotient_span (mul_ne_zero (modulus_ne_zero I) (modulus_ne_zero J))
  let : Fintype (O ⧸ Ideal.span {a*b}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {a})*(Ideal.span {b})) := finite_quotient_product (modulus_ne_zero I) (modulus_ne_zero J)
  let : Fintype (O ⧸ (Ideal.span {a})*(Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span (modulus_ne_zero J)
  let e : (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ (Ideal.span {a})*(Ideal.span {b})) :=
    Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm
  dsimp only [principalNormalizedGauss, pairGauss, ConcreteBreveE.normalizedTraceGaussProduct]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  change principalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) * _ = _
  rw [principalRow_mk I J hI hJ hfI hfJ hcop]
  simp only [e, a, b, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]
  rw [← MulChar.star_apply', character_mk I hI hfI, character_mk J hJ hfJ]
  congr 1

/-- Poisson for a coprime pair of sixth-power-free columns. The modulus is
the product of their radicals, and the Gauss multiplier retains its coupling. -/
theorem pair_poisson (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    (∑' z : O, (idealRowHom z I * star (idealRowHom z J)) * W (‖eisEmbedding z‖^2 / A)) =
      ((A : ℂ) * pairGauss I J hI hJ / (‖eisEmbedding (modulus I * modulus J)‖ : ℂ)) *
      ∑' k : O, (star (idealRowHom k I) * idealRowHom k J) *
        paperRadialFourier W (A * ‖eisEmbedding k‖^2 /
          ‖eisEmbedding (modulus I * modulus J)‖^2) := by
  let c := modulus I * modulus J
  have hc0 : c ≠ 0 := mul_ne_zero (modulus_ne_zero I) (modulus_ne_zero J)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (product_modulus I J)
  let : Fintype (O ⧸ ∏ P, primes I J P) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (P : PrimeIndex I ⊕ PrimeIndex J) : Fintype (O ⧸ primes I J P) := Fintype.ofFinite _
  let row := principalRow I J hI hJ hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  let G := ∑ r : O ⧸ Ideal.span {c}, row r * ψ r
  have ht (k : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) k * r)) =
        (star (idealRowHom k I) * idealRowHom k J) * G := by
    have hh := canonical_principal_gauss_transform (primes I J)
      (primes_coprime I J hI hJ hcop) (primes_good I J hI hJ) (primes_odd I J hI hJ)
      (exponents I J) (fun P => (exponents_range I J hI hJ hfI hfJ P).1)
      (fun P => (exponents_range I J hI hJ hfI hfJ P).2)
      c (product_modulus I J) ψ (Ideal.Quotient.mk (Ideal.span {c}) k)
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) k * r)) =
      star (principalRow I J hI hJ hcop (Ideal.Quotient.mk _ k)) * G at hh
    rw [principalRow_mk I J hI hJ hfI hfJ hcop, star_mul, star_star] at hh
    simpa only [mul_comm (idealRowHom k J) (star (idealRowHom k I))] using hh
  have hp := actual_radial_paper_poisson_trace W A hA c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖^2 / A)) =
    (A / ‖eisEmbedding c‖^2 : ℝ) • ∑' k : O,
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) k * r)) *
        paperRadialFourier W (A * ‖eisEmbedding k‖^2 / ‖eisEmbedding c‖^2) at hp
  simp_rw [ht] at hp
  have hsum : (∑' k : O, ((star (idealRowHom k I) * idealRowHom k J) * G) *
      paperRadialFourier W (A * ‖eisEmbedding k‖^2 / ‖eisEmbedding c‖^2)) =
      G * ∑' k : O, (star (idealRowHom k I) * idealRowHom k J) *
        paperRadialFourier W (A * ‖eisEmbedding k‖^2 / ‖eisEmbedding c‖^2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  rw [hsum] at hp
  have hrow (z : O) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      idealRowHom z I * star (idealRowHom z J) := principalRow_mk I J hI hJ hfI hfJ hcop z
  simp_rw [hrow] at hp
  rw [hp]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc0))
  have hGauss := principalGauss_eq I J hI hJ hfI hfJ hcop
  change G / (‖eisEmbedding c‖ : ℂ) = pairGauss I J hI hJ at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((A / ‖eisEmbedding c‖^2 : ℝ) : ℂ) * (G * _) = _
  rw [← mul_assoc]
  congr 1
  change ((A / ‖eisEmbedding c‖^2 : ℝ) : ℂ) * G =
    (A : ℂ) * pairGauss I J hI hJ / (‖eisEmbedding c‖ : ℂ)
  rw [hG]
  push_cast
  field_simp [hn]

theorem pair_fourier_summable (I J : Id) (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun k : O => (star (idealRowHom k I) * idealRowHom k J) *
      paperRadialFourier W (t * ‖eisEmbedding k‖^2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro k
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm k I)).trans
      (idealRowHom_norm k J)) (norm_nonneg _)).trans_eq (one_mul _)

def dualTerm (I J : Id) (hI : Supported I) (hJ : Supported J)
    (a b : ℂ) (W : 𝓢(ℝ, ℂ)) (A : ℝ) (k : O) : ℂ :=
  (a * star b * pairGauss I J hI hJ / (‖eisEmbedding (modulus I * modulus J)‖ : ℂ)) *
    ((star (idealRowHom k I) * idealRowHom k J) *
      paperRadialFourier W (A * ‖eisEmbedding k‖^2 / ‖eisEmbedding (modulus I * modulus J)‖^2))

theorem dualTerm_summable (I J : Id) (hI : Supported I) (hJ : Supported J)
    (a b : ℂ) (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    Summable (dualTerm I J hI hJ a b W A) := by
  have hn : 0 < ‖eisEmbedding (modulus I * modulus J)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (mul_ne_zero (modulus_ne_zero I) (modulus_ne_zero J)))
  have hs := (pair_fourier_summable I J W
    (A / ‖eisEmbedding (modulus I * modulus J)‖^2) (by positivity)).mul_left
      (a * star b * pairGauss I J hI hJ / (‖eisEmbedding (modulus I * modulus J)‖ : ℂ))
  convert hs using 1
  ext k
  dsimp [dualTerm]
  congr 3
  ring

/-- Interchanging the whole finite column family with Poisson's infinite
frequency sum is justified by absolute summability, not by a formal rewrite. -/
theorem family_poisson {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    (∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
      a i * star (a j) * ∑' z : O,
        (idealRowHom z (cols i) * star (idealRowHom z (cols j))) * W (‖eisEmbedding z‖^2/A)
      else 0) =
      (A : ℂ) * ∑' k : O, ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
        dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (a j) W A k else 0 := by
  have hs (i j : n) : Summable (fun k : O => if IsCoprime (cols i) (cols j) then
      dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (a j) W A k else 0) := by
    split_ifs
    · exact dualTerm_summable _ _ _ _ _ _ _ _ hA
    · exact summable_zero
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  simp_rw [Summable.tsum_finsetSum (fun j _ => hs _ j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hcop : IsCoprime (cols i) (cols j)
  · simp only [ite_eq_left hcop]
    rw [pair_poisson _ _ (hc i) (hc j) (hf i) (hf j) hcop W A hA]
    simp only [dualTerm, tsum_mul_left]
    ring
  · simp only [ite_eq_right hcop, tsum_zero, mul_zero]

end
end Candidate.Feedback.FourthPower.SievePairPoisson
