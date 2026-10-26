/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.GoodIdealMass

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid

theorem valuation_prime (P : PrimeIdeal) (Q : Ideal O) :
    valuation P.val Q = if Q=P.val then 1 else 0 := by
  simp [valuation,factorization_eq_count,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton]

theorem valuation_pow (I P : Ideal O) (n : ℕ) : valuation (I^n) P = n*valuation I P := by
  simp [valuation,factorization_pow]

theorem valuation_prod {α : Type*} (S : Finset α) (g : α → Ideal O)
    (h : ∀ a ∈ S, g a ≠ 0) (P : Ideal O) :
    valuation (∏ a ∈ S, g a) P = ∑ a ∈ S, valuation (g a) P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,factorization_one,Finsupp.zero_apply]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,
      valuation_mul (h a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun b hb => h b (Finset.mem_insert_of_mem hb))),
      ih (fun b hb => h b (Finset.mem_insert_of_mem hb))]

def decode (S : Finset PrimeIdeal) (a : S → ℕ) : Ideal O := ∏ P : S, P.val.val^(a P)

theorem decode_ne_zero (S : Finset PrimeIdeal) (a : S → ℕ) : decode S a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ P.val.property.ne_zero

theorem valuation_decode (S : Finset PrimeIdeal) (a : S → ℕ) (P : S) :
    valuation (decode S a) P.val.val = a P := by
  classical
  rw [decode,valuation_prod _ _ (fun Q _ => pow_ne_zero _ Q.val.property.ne_zero)]
  simp_rw [valuation_pow,valuation_prime]
  rw [Finset.sum_eq_single P]
  · simp
  · intro Q hQ hQP
    rw [ite_eq_right (by
      intro heq
      apply hQP
      apply Subtype.ext
      exact Subtype.ext heq.symm),mul_zero]
  · simp

theorem valuation_decode_outside (S : Finset PrimeIdeal) (a : S → ℕ) (P : Ideal O)
    (hP : P ∉ primeValues S) : valuation (decode S a) P=0 := by
  rw [decode,valuation_prod _ _ (fun Q _ => pow_ne_zero _ Q.val.property.ne_zero)]
  apply Finset.sum_eq_zero
  intro Q hQ
  rw [valuation_pow,valuation_prime,ite_eq_right (by
    intro heq
    exact hP (Finset.mem_image.mpr ⟨Q.val,Q.property,heq.symm⟩)),mul_zero]

theorem decode_support (S : Finset PrimeIdeal) (a : S → ℕ) :
    primeSupport (decode S a) ⊆ primeValues S := by
  intro P hP
  by_contra hn
  have hz := valuation_decode_outside S a P hn
  have hm : P ∈ (factorization (decode S a)).support := by
    simpa only [support_factorization,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using hP
  exact (Finsupp.mem_support_iff.mp hm) hz

theorem decode_encode (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0)
    (hS : primeSupport I ⊆ primeValues S) :
    decode S (fun P => valuation I P.val.val) = I := by
  apply ideals_eq_of_valuations_on (decode_ne_zero _ _) hI (primeValues S) (decode_support _ _) hS
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  exact valuation_decode S _ ⟨Q,hQ⟩

theorem dvd_iff_valuation_le {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ∣ J ↔ ∀ P, valuation I P ≤ valuation J P := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hI hJ,Multiset.le_iff_count]
  rfl


theorem primeSupport_subset_of_dvd {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) (h : I ∣ J) :
    primeSupport I ⊆ primeSupport J := by
  intro P hP
  have hm : P ∈ (normalizedFactors I) := Multiset.mem_toFinset.mp hP
  exact Multiset.mem_toFinset.mpr
    (Multiset.mem_of_le (dvd_iff_normalizedFactors_le_normalizedFactors hI hJ |>.mp h) hm)

def pairBox (S : Finset PrimeIdeal) (I J : Ideal O) : Finset (S → ℕ×ℕ) :=
  Fintype.piFinset (fun P : S => Finset.range (valuation I P.val.val+1) ×ˢ
    Finset.range (valuation J P.val.val+1))

def decodePair (S : Finset PrimeIdeal) (a : S → ℕ×ℕ) : Ideal O × Ideal O :=
  (decode S (fun P => (a P).1),decode S (fun P => (a P).2))

theorem decodePair_encodePair (S : Finset PrimeIdeal) (d : Ideal O × Ideal O)
    (hnz : d.1 ≠ 0 ∧ d.2 ≠ 0) (hs : pairSupport d.1 d.2 ⊆ primeValues S) :
    decodePair S (encodePair S d) = d := by
  apply Prod.ext
  · exact decode_encode S hnz.1 (Finset.Subset.trans Finset.subset_union_left hs)
  · exact decode_encode S hnz.2 (Finset.Subset.trans Finset.subset_union_right hs)

theorem encodePair_decodePair (S : Finset PrimeIdeal) (a : S → ℕ×ℕ) :
    encodePair S (decodePair S a) = a := by
  funext P
  apply Prod.ext <;> exact valuation_decode S _ P

theorem decodePair_injective (S : Finset PrimeIdeal) : Function.Injective (decodePair S) := by
  intro a b h
  have he := congrArg (encodePair S) h
  simpa only [encodePair_decodePair] using he

theorem decodePair_mem_divisors {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) {a : S → ℕ×ℕ} (ha : a ∈ pairBox S I J) :
    decodePair S a ∈ OAI.IdealMobiusDivisorSum.idealDivisors I ×ˢ
      OAI.IdealMobiusDivisorSum.idealDivisors J := by
  simp only [pairBox,Fintype.mem_piFinset,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff] at ha
  apply Finset.mem_product.mpr
  constructor
  · apply (OAI.IdealMobiusDivisorSum.mem_idealDivisors hI).mpr
    apply (dvd_iff_valuation_le (decode_ne_zero _ _) hI).mpr
    intro P
    by_cases hp : P ∈ primeValues S
    · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hp
      exact (valuation_decode S (fun P => (a P).1) ⟨Q,hQ⟩).trans_le (ha ⟨Q,hQ⟩).1
    · rw [valuation_decode_outside S _ P hp]
      exact Nat.zero_le _
  · apply (OAI.IdealMobiusDivisorSum.mem_idealDivisors hJ).mpr
    apply (dvd_iff_valuation_le (decode_ne_zero _ _) hJ).mpr
    intro P
    by_cases hp : P ∈ primeValues S
    · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hp
      exact (valuation_decode S (fun P => (a P).2) ⟨Q,hQ⟩).trans_le (ha ⟨Q,hQ⟩).2
    · rw [valuation_decode_outside S _ P hp]
      exact Nat.zero_le _

theorem divisor_pair_enumeration {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport I J ⊆ primeValues S) :
    (pairBox S I J).image (decodePair S) =
      OAI.IdealMobiusDivisorSum.idealDivisors I ×ˢ OAI.IdealMobiusDivisorSum.idealDivisors J := by
  classical
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    exact decodePair_mem_divisors hI hJ S ha
  · intro d hd
    obtain ⟨hdi,hdj⟩ := Finset.mem_product.mp hd
    have hi := (OAI.IdealMobiusDivisorSum.mem_idealDivisors hI).mp hdi
    have hj := (OAI.IdealMobiusDivisorSum.mem_idealDivisors hJ).mp hdj
    have hdi0 : d.1 ≠ 0 := ne_zero_of_dvd_ne_zero hI hi
    have hdj0 : d.2 ≠ 0 := ne_zero_of_dvd_ne_zero hJ hj
    have hds : pairSupport d.1 d.2 ⊆ primeValues S := by
      apply Finset.Subset.trans (Finset.union_subset_union
        (primeSupport_subset_of_dvd hdi0 hI hi) (primeSupport_subset_of_dvd hdj0 hJ hj)) hs
    refine Finset.mem_image.mpr ⟨encodePair S d,?_,decodePair_encodePair S d ⟨hdi0,hdj0⟩ hds⟩
    simp only [pairBox,Fintype.mem_piFinset,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
    intro P
    exact ⟨(dvd_iff_valuation_le hdi0 hI).mp hi _,(dvd_iff_valuation_le hdj0 hJ).mp hj _⟩

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.decode_encode
