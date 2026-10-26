/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual nonzero tuple witnesses justify squarefreeness at amplifier primes.
Norm geometry supplies the finite divisor count used by the exact correction. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedDensity
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SourceModifier

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentAmplificationCount CenteredMomentAmplificationSlotGap
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem source_column_no_prime_square
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (β : Tuple ι→ℂ) (I Q : Ideal O) (hQ : Prime Q)
    (hmarked : ∀i,∀J∈S (Sum.inl i),¬Q∣J)
    (hne : finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>sourceModifier A₁ A₂ D F v*β v) I≠0) : ¬Q^2∣I := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have hsf := (sourceModifier_nonzero A₁ A₂ D F v (mul_ne_zero_iff.mp hvn).1).2.1
  have heq : A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)=
      (A₁*A₂)*(v (Sum.inr 0)*v (Sum.inr 1)) := by ring
  rw [heq] at hsf
  have hslot : ¬Q∣∏i,v (Sum.inl i) := by
    apply hQ.not_dvd_finsetProd
    intro i hi
    exact hmarked i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  rw [←he]
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two]
  simpa only [mul_assoc] using no_prime_square_dvd_column hQ hsf.of_mul_right hslot

theorem source_divisor_no_prime_square
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (β : Tuple ι→ℂ) (I J Q : Ideal O) (hQ : Prime Q)
    (hmarked : ∀i,∀J∈S (Sum.inl i),¬Q∣J) (hJI : J∣I)
    (hne : finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>sourceModifier A₁ A₂ D F v*β v) I≠0) : ¬Q^2∣J :=
  prime_square_exclusion_of_dvd
    (source_column_no_prime_square S A₁ A₂ D F β I Q hQ hmarked hne) hJI

theorem element_square_exclusion_of_span (p a : O)
    (h : ¬(Ideal.span {p})^2∣Ideal.span {a}) : ¬p^2∣a := by
  intro hp
  apply h
  rw [Ideal.dvd_iff_le,Ideal.span_singleton_pow,Ideal.span_singleton_le_span_singleton]
  exact hp

theorem source_generator_no_prime_square (S : Finset (Ideal O)) (I : supportedColumns S)
    (p : O) (h : ¬(Ideal.span {p})^2∣I.val) : ¬p^2∣sourceGenerator S I := by
  apply element_square_exclusion_of_span
  simpa only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2] using h

/-- No distinctness assumption on generators is hidden: primary normalization
identifies two generators of the same ideal before counting prime divisors. -/
theorem dividingPool_card_le_norm (P : Finset O) (a : O) (ha : a≠0)
    (hp : ∀p∈P,Prime p) (hprimary : ∀p∈P,goodLambda^2∣p-1)
    (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(Ideal.absNorm (Ideal.span {p}):ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {a}):ℝ)≤Z^B) :
    ((dividingPool P a).card:ℝ)≤B/ell := by
  apply indexed_large_prime_divisor_count (dividingPool P a) (fun p=>Ideal.span {p}) ?_
    (fun p h=>CubicEisenstein.gaussPrimeIdeal_prime p (hp p (Finset.mem_filter.mp h).1))
    (Ideal.span {a}) (Ideal.span_singleton_eq_bot.not.mpr ha) ?_ Z ell B hZ hell
    (fun p h=>hlower p (Finset.mem_filter.mp h).1) hupper
  · intro p hp' q hq' he
    have hpP := (Finset.mem_filter.mp hp').1
    have hqP := (Finset.mem_filter.mp hq').1
    rw [←CompletedGauss.primaryGenerator_span p (hp p hpP).ne_zero (hprimary p hpP),
      ←CompletedGauss.primaryGenerator_span q (hp q hqP).ne_zero (hprimary q hqP)]
    exact congrArg CompletedGauss.primaryGenerator he
  · intro p hp'
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]
    exact (Finset.mem_filter.mp hp').2

theorem dividingPool_card_lt_of_geometry (P : Finset O) (hP : P.Nonempty)
    (a : O) (ha : a≠0) (hp : ∀p∈P,Prime p) (hprimary : ∀p∈P,goodLambda^2∣p-1)
    (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(Ideal.absNorm (Ideal.span {p}):ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {a}):ℝ)≤Z^B)
    (hsize : 2*(B/ell)≤(P.card:ℝ)) : (dividingPool P a).card<P.card := by
  have hcount := dividingPool_card_le_norm P a ha hp hprimary Z ell B hZ hell hlower hupper
  have hhalf : 2*(dividingPool P a).card≤P.card := by
    exact_mod_cast (show (2:ℝ)*((dividingPool P a).card:ℝ)≤P.card by linarith)
  have hpos := hP.card_pos
  omega

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.source_column_no_prime_square
#print axioms OAI.SevenEighths.Record1252270103Source.source_generator_no_prime_square
#print axioms OAI.SevenEighths.Record1252270103Source.dividingPool_card_lt_of_geometry
