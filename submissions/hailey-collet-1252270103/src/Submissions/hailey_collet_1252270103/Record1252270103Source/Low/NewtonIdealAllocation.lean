/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonIdealCounts
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
local notation "O" => ActualEisensteinCubic.O

/-- A prime cannot belong to both ordinary factors of a squarefree product. -/
theorem squarefree_prime_exclusive (p I J : Ideal O) (hp : Prime p)
    (hsf : Squarefree (I*J)) : ¬(p∣I ∧ p∣J) := by
  rintro ⟨hI,hJ⟩
  exact hp.not_isUnit (hsf p (mul_dvd_mul hI hJ))

theorem ideal_prime_indicator_split (p I J : Ideal O) (hp : Prime p)
    (hsf : Squarefree (I*J)) :
    idealDvdIndicator p (I*J)=idealDvdIndicator p I+idealDvdIndicator p J := by
  have hex := squarefree_prime_exclusive p I J hp hsf
  by_cases hI : p∣I <;> by_cases hJ : p∣J
  · exact (hex ⟨hI,hJ⟩).elim
  · simp [idealDvdIndicator,hp.dvd_mul,hI,hJ]
  · simp [idealDvdIndicator,hp.dvd_mul,hI,hJ]
  · simp [idealDvdIndicator,hp.dvd_mul,hI,hJ]

theorem ideal_set_indicator_prod (S : Finset (Ideal O)) (I : Ideal O) :
    idealSetIndicator S I=∏p∈S,idealDvdIndicator p I := by
  simp [idealSetIndicator,idealDvdIndicator,Finset.prod_ite_zero]

/-- Exact assignments of the selected primes to the two original factors.
Squarefreeness removes the possible double assignment. -/
theorem ideal_set_indicator_assignments (S : Finset (Ideal O)) (I J : Ideal O)
    (hp : ∀p∈S,Prime p) (hsf : Squarefree (I*J)) :
    idealSetIndicator S (I*J)=
      ∑A∈S.powerset,idealSetIndicator A I*idealSetIndicator (S\A) J := by
  rw [ideal_set_indicator_prod]
  calc
    (∏p∈S,idealDvdIndicator p (I*J)) =
        ∏p∈S,(idealDvdIndicator p I+idealDvdIndicator p J) := by
      apply Finset.prod_congr rfl
      intro p hm
      exact ideal_prime_indicator_split p I J (hp p hm) hsf
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro A _
      rw [ideal_set_indicator_prod,ideal_set_indicator_prod]

/-- Distinct prime ideals in this Dedekind ring are coprime. -/
theorem prime_ideal_finset_pairwise (S : Finset (Ideal O)) (hp : ∀p∈S,Prime p) :
    (S : Set (Ideal O)).Pairwise (fun p q=>IsCoprime p q) := by
  intro p hm q hn hne
  letI : p.IsMaximal := (Ideal.isPrime_of_prime (hp p hm)).isMaximal (hp p hm).ne_zero
  letI : q.IsMaximal := (Ideal.isPrime_of_prime (hp q hn)).isMaximal (hp q hn).ne_zero
  exact Ideal.isCoprime_of_isMaximal hne

theorem prime_ideal_product_dvd_iff (S : Finset (Ideal O)) (I : Ideal O)
    (hp : ∀p∈S,Prime p) : (∏p∈S,p)∣I ↔ ∀p∈S,p∣I := by
  constructor
  · intro h p hm
    exact (Finset.dvd_prod_of_mem (fun p : Ideal O=>p) hm).trans h
  · exact Finset.prod_dvd_of_coprime (prime_ideal_finset_pairwise S hp)

theorem ideal_set_indicator_eq_product (S : Finset (Ideal O)) (I : Ideal O)
    (hp : ∀p∈S,Prime p) :
    idealSetIndicator S I=idealDvdIndicator (∏p∈S,p) I := by
  simp only [idealSetIndicator,idealDvdIndicator,prime_ideal_product_dvd_iff S I hp]

/-- The assignment formula uses actual ideal-product divisibility projectors. -/
theorem ideal_product_projector_assignments (S : Finset (Ideal O)) (I J : Ideal O)
    (hp : ∀p∈S,Prime p) (hsf : Squarefree (I*J)) :
    idealDvdIndicator (∏p∈S,p) (I*J)=
      ∑A∈S.powerset,
        idealDvdIndicator (∏p∈A,p) I*idealDvdIndicator (∏p∈S\A,p) J := by
  rw [←ideal_set_indicator_eq_product S (I*J) hp,
    ideal_set_indicator_assignments S I J hp hsf]
  apply Finset.sum_congr rfl
  intro A hA
  rw [ideal_set_indicator_eq_product A I (fun p hm=>hp p (Finset.mem_powerset.mp hA hm)),
    ideal_set_indicator_eq_product (S\A) J (fun p hm=>hp p (Finset.mem_sdiff.mp hm).1)]

/-- Off-support this remains a finite polynomial. On squarefree ordinary pairs
it is exactly a finite sum of rectangular divisibility projectors. -/
theorem idealNewtonPolynomial_assignments (P : Finset (Ideal O)) (r0 depth : ℕ)
    (I J : Ideal O) (hp : ∀p∈P,Prime p) (hsf : Squarefree (I*J)) :
    idealNewtonPolynomial P r0 depth (I*J)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),
        ∑A∈S.powerset,newtonCoefficient P.card r0 S.card *
          (idealDvdIndicator (∏p∈A,p) I*idealDvdIndicator (∏p∈S\A,p) J) := by
  unfold idealNewtonPolynomial
  apply Finset.sum_congr rfl
  intro S hS
  have hs : ∀p∈S,Prime p := fun p hm=>hp p
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hm)
  rw [ideal_set_indicator_eq_product S (I*J) hs,
    ideal_product_projector_assignments S I J hs hsf,Finset.mul_sum]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.squarefree_prime_exclusive
#print axioms QRH.Record1252270103Low.ideal_product_projector_assignments
#print axioms QRH.Record1252270103Low.idealNewtonPolynomial_assignments
