/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual squarefree ordinary columns and disjoint marked pools force the four
first-common valuation types. No cancellation of character zeros is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CoupledProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103CommonGeometry
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal Record1252270103Source
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredExceptionalCount
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

/-- This predicate concerns actual prime-ideal valuations, including primes
outside a chosen common support. -/
def ValuationAtMostTwo (I : Ideal O) : Prop :=
  ∀ P : Ideal O, Prime P → valuation I P ≤ 2

theorem valuation_le_two_of_no_cube (I P : Ideal O) (hI : I≠0)
    (hP : Prime P) (hcube : ¬P^3∣I) : valuation I P≤2 := by
  rw [valuation_eq_multiplicity hI hP]
  have hfin := FiniteMultiplicity.of_prime_left hP hI
  have hh := (hfin.pow_dvd_iff_le_multiplicity (k := 3)).not.mp hcube
  omega

theorem two_squarefree_valuation_bound (S I : Ideal O)
    (hS : Squarefree S) (hI : Squarefree I) : ValuationAtMostTwo (S*I) := by
  intro P hP
  exact valuation_le_two_of_no_cube _ _ (mul_ne_zero hS.ne_zero hI.ne_zero) hP
    (no_prime_cube_dvd_two_squarefree hP hS hI)

theorem valuation_bound_of_dvd (I C : Ideal O) (hI : I≠0)
    (hC : C∣I) (hbound : ValuationAtMostTwo I) : ValuationAtMostTwo C := by
  have hC0 : C≠0 := ne_zero_of_dvd_ne_zero hI hC
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hC0 hI).mp hC
  intro P hP
  exact (Multiset.le_iff_count.mp hle P).trans (hbound P hP)

theorem marked_product_squarefree {ι : Type*} [Fintype ι]
    (pool : ι→Finset (Ideal O)) (v : ι→Ideal O)
    (hprime : ∀i,∀P∈pool i,Prime P)
    (hdisjoint : Pairwise (Function.onFun Disjoint pool))
    (hv : ∀i,v i∈pool i) : Squarefree (∏i,v i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    letI : (v i).IsMaximal := (Ideal.isPrime_of_prime (hprime i _ (hv i))).isMaximal
      (hprime i _ (hv i)).ne_zero
    letI : (v j).IsMaximal := (Ideal.isPrime_of_prime (hprime j _ (hv j))).isMaximal
      (hprime j _ (hv j)).ne_zero
    apply (Ideal.isCoprime_of_isMaximal (I:=v i) (J:=v j) ?_).isRelPrime
    intro he
    exact Finset.disjoint_left.mp (hdisjoint hij) (hv i) (he ▸ hv j)
  · intro i hi
    exact (hprime i _ (hv i)).squarefree

theorem tuple_valuation_bound {ι : Type*} [Fintype ι]
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (hd : Pairwise (Function.onFun Disjoint (fun i=>S (Sum.inl i))))
    (v : Tuple ι) (hv : v∈Fintype.piFinset S)
    (hsf : Squarefree (v (Sum.inr 0)*v (Sum.inr 1))) :
    ValuationAtMostTwo (finiteTupleProduct v) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two]
  apply two_squarefree_valuation_bound _ _ _ hsf
  exact marked_product_squarefree (fun i=>S (Sum.inl i)) (fun i=>v (Sum.inl i))
    hp hd (fun i=>Fintype.mem_piFinset.mp hv (Sum.inl i))

/-- A nonzero finite column has an actual nonzero summand. The squarefree
projector on that summand, rather than an unmasked source coefficient,
supplies the valuation restriction. All multiplier zeros are retained. -/
theorem coupled_column_valuation_bound {ι : Type*} [Fintype ι]
    (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (hd : Pairwise (Function.onFun Disjoint (fun i=>S (Sum.inl i))))
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (hne : finiteColumnCoefficient (Fintype.piFinset S)
      (coupledProfile A₁ A₂ D F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    ValuationAtMostTwo I := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have hsf : Squarefree (A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)) := by
    by_contra h
    exact hvn (by simp [coupledProfile,coupledFactor,squarefreeIndicator,h])
  have hsf' : Squarefree (v (Sum.inr 0)*v (Sum.inr 1)) := by
    have heq : A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)=
        (A₁*A₂)*(v (Sum.inr 0)*v (Sum.inr 1)) := by ring
    rw [heq] at hsf
    exact hsf.of_mul_right
  rw [←he]
  exact tuple_valuation_bound S hp hd v hv hsf'

theorem common_four_types (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) (P : CommonIndex C D) :
    (leftExponent C D P=1 ∧ rightExponent C D P=1) ∨
    (leftExponent C D P=1 ∧ rightExponent C D P=2) ∨
    (leftExponent C D P=2 ∧ rightExponent C D P=1) ∨
    (leftExponent C D P=2 ∧ rightExponent C D P=2) := by
  have hp : Prime P.val := prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)
  have hc := hC P.val hp
  have hd := hD P.val hp
  have hcp := leftExponent_pos C D P
  have hdp := rightExponent_pos C D P
  change leftExponent C D P≤2 at hc
  change rightExponent C D P≤2 at hd
  omega

theorem extracted_four_types (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hbI : ValuationAtMostTwo I) (hbJ : ValuationAtMostTwo J)
    (P : CommonIndex (commonPart I J) (commonPart J I)) :
    (leftExponent _ _ P=1 ∧ rightExponent _ _ P=1) ∨
    (leftExponent _ _ P=1 ∧ rightExponent _ _ P=2) ∨
    (leftExponent _ _ P=2 ∧ rightExponent _ _ P=1) ∨
    (leftExponent _ _ P=2 ∧ rightExponent _ _ P=2) :=
  common_four_types _ _ (valuation_bound_of_dvd I _ hI (commonPart_dvd I J hI) hbI)
    (valuation_bound_of_dvd J _ hJ (commonPart_dvd J I hJ) hbJ) P

end
end OAI.SevenEighths.Record1252270103CommonGeometry

#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.coupled_column_valuation_bound
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.extracted_four_types
