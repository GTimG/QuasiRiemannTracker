/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairClearing
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.IdealFactorization

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- This is cubefreeness of the product, so it permits a prime in both ideals. -/
def PairCubeFree (I J : Ideal O) : Prop :=
  ∀ P : PrimeIdeal, ProbePhysical.primeValuations I P+ProbePhysical.primeValuations J P ≤ 2

def pairPrimeSupport (I J : Ideal O) : Finset PrimeIdeal :=
  (ProbePhysical.primeValuations I).support ∪ (ProbePhysical.primeValuations J).support

lemma valuation_zero_outside_pairSupport (I J : Ideal O) (P : PrimeIdeal)
    (hP : P ∉ pairPrimeSupport I J) :
    ProbePhysical.primeValuations I P=0 ∧ ProbePhysical.primeValuations J P=0 := by
  have h : P ∉ (ProbePhysical.primeValuations I).support ∧ P ∉ (ProbePhysical.primeValuations J).support := by
    simpa only [pairPrimeSupport,Finset.mem_union,not_or] using hP
  exact ⟨Finsupp.notMem_support_iff.mp h.1,Finsupp.notMem_support_iff.mp h.2⟩

lemma idealCoeff_valuation_product (ψ : Character) (I : Ideal O) (hI : I ≠ 0)
    (S : Finset PrimeIdeal) (hS : (ProbePhysical.primeValuations I).support ⊆ S) :
    (∏ P ∈ S,idealCoeff ψ P.val^ProbePhysical.primeValuations I P)=idealCoeff ψ I := by
  conv_rhs => rw [←ProbePhysical.idealFromValuations_primeValuations I hI]
  simp only [ProbePhysical.idealFromValuations,Finsupp.prod,map_prod,map_pow]
  exact (Finset.prod_subset hS (fun P _ hP => by
    rw [Finsupp.notMem_support_iff.mp hP,pow_zero])).symm

/-- The coefficient of a specified pair of nonzero ideals in the product of
H9 and the two ordinary geometric series. -/
def goodPairEulerCoefficient (ψ₁ ψ₂ : Character) (I J : Ideal O) : ℂ :=
  ∏ P ∈ pairPrimeSupport I J,
    ((idealCoeff ψ₁ P.val)^ProbePhysical.primeValuations I P*
      (idealCoeff ψ₂ P.val)^ProbePhysical.primeValuations J P +
    ∑ j : Fin 7, if (h3Exponent j).1 ≤ ProbePhysical.primeValuations I P ∧
      (h3Exponent j).2 ≤ ProbePhysical.primeValuations J P then
      h3Term (idealCoeff ψ₁ P.val) (idealCoeff ψ₂ P.val) j*
        (idealCoeff ψ₁ P.val)^(ProbePhysical.primeValuations I P-(h3Exponent j).1)*
        (idealCoeff ψ₂ P.val)^(ProbePhysical.primeValuations J P-(h3Exponent j).2) else 0)

theorem goodPairEulerCoefficient_eq (ψ₁ ψ₂ : Character) (I J : Ideal O)
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    goodPairEulerCoefficient ψ₁ ψ₂ I J =
      if PairCubeFree I J then idealCoeff ψ₁ I*idealCoeff ψ₂ J else 0 := by
  unfold goodPairEulerCoefficient
  simp_rw [goodLocal_convolution]
  by_cases h : PairCubeFree I J
  · rw [ite_eq_left h]
    simp only [ite_eq_left (h _),Finset.prod_mul_distrib]
    rw [idealCoeff_valuation_product ψ₁ I hI (pairPrimeSupport I J)
      (show (ProbePhysical.primeValuations I).support ⊆ pairPrimeSupport I J from Finset.subset_union_left),
      idealCoeff_valuation_product ψ₂ J hJ (pairPrimeSupport I J)
      (show (ProbePhysical.primeValuations J).support ⊆ pairPrimeSupport I J from Finset.subset_union_right)]
  · rw [ite_eq_right h]
    obtain ⟨P,hP⟩ := not_forall.mp h
    have hm : P ∈ pairPrimeSupport I J := by
      by_contra hn
      obtain ⟨hi,hj⟩ := valuation_zero_outside_pairSupport I J P hn
      simp [hi,hj] at hP
    exact Finset.prod_eq_zero hm (ite_eq_right hP)

/-- Original coupled support, with the actual residual valuation holes at
each exceptional prime. -/
def PairAllowed (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (I J : Ideal O) : Prop :=
  (∀ P : PrimeIdeal, P ∉ bad → ProbePhysical.primeValuations I P+
    ProbePhysical.primeValuations J P ≤ 2) ∧
  (∀ P ∈ bad,(ProbePhysical.primeValuations I P,ProbePhysical.primeValuations J P) ∈ allowed P)

/-- A finite coefficient extraction from H10 with the exceptional Euler
factors removed from the authentic ordinary characters first. -/
def correctedPairEulerCoefficient (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) : ℂ :=
  (∏ P ∈ pairPrimeSupport I J \ bad,
    ((idealCoeff χ₁ P.val)^ProbePhysical.primeValuations I P*
      (idealCoeff χ₂ P.val)^ProbePhysical.primeValuations J P +
    ∑ j : Fin 7, if (h3Exponent j).1 ≤ ProbePhysical.primeValuations I P ∧
      (h3Exponent j).2 ≤ ProbePhysical.primeValuations J P then
      h3Term (idealCoeff ψ₁ P.val) (idealCoeff ψ₂ P.val) j*
        (idealCoeff χ₁ P.val)^(ProbePhysical.primeValuations I P-(h3Exponent j).1)*
        (idealCoeff χ₂ P.val)^(ProbePhysical.primeValuations J P-(h3Exponent j).2) else 0)) *
  ∏ P ∈ bad, ∑ q ∈ allowed P, ∑ j : Fin 4,
    if q.1+deletionExponent₁ j ≤ ProbePhysical.primeValuations I P ∧
      q.2+deletionExponent₂ j ≤ ProbePhysical.primeValuations J P then
      ((idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)*
        deletionTerm (idealCoeff χ₁ P.val) (idealCoeff χ₂ P.val) j*
        (idealCoeff χ₁ P.val)^(ProbePhysical.primeValuations I P-q.1-deletionExponent₁ j)*
        (idealCoeff χ₂ P.val)^(ProbePhysical.primeValuations J P-q.2-deletionExponent₂ j) else 0

lemma correctedPairEulerCoefficient_local (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (I J : Ideal O) :
    correctedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J =
      (∏ P ∈ pairPrimeSupport I J \ bad,
        if ProbePhysical.primeValuations I P+ProbePhysical.primeValuations J P ≤ 2 then
          (idealCoeff ψ₁ P.val)^ProbePhysical.primeValuations I P*
          (idealCoeff ψ₂ P.val)^ProbePhysical.primeValuations J P else 0) *
      ∏ P ∈ bad, if (ProbePhysical.primeValuations I P,ProbePhysical.primeValuations J P) ∈ allowed P then
        (idealCoeff ψ₁ P.val)^ProbePhysical.primeValuations I P*
          (idealCoeff ψ₂ P.val)^ProbePhysical.primeValuations J P else 0 := by
  unfold correctedPairEulerCoefficient
  congr 1
  · apply Finset.prod_congr rfl
    intro P hP
    have hn := (Finset.mem_sdiff.mp hP).2
    rw [hχ₁ P hn,hχ₂ P hn,goodLocal_convolution]
  · apply Finset.prod_congr rfl
    intro P _
    exact exceptionalLocal_convolution _ _ _ _ _ _ _

lemma ideal_dvd_iff_valuations_le (A B : Ideal O) (hA : A ≠ 0) (hB : B ≠ 0) :
    A ∣ B ↔ ProbePhysical.primeValuations A ≤ ProbePhysical.primeValuations B := by
  constructor
  · rintro ⟨D,hD⟩
    have hn : D ≠ 0 := by intro he; simp [he] at hD; exact hB hD
    rw [hD,ProbePhysical.primeValuations_mul A D hA hn]
    intro P
    exact Nat.le_add_right _ _
  · intro h
    refine ⟨ProbePhysical.idealFromValuations
      (ProbePhysical.primeValuations B-ProbePhysical.primeValuations A),?_⟩
    calc
      B = ProbePhysical.idealFromValuations (ProbePhysical.primeValuations B) :=
        (ProbePhysical.idealFromValuations_primeValuations B hB).symm
      _ = ProbePhysical.idealFromValuations (ProbePhysical.primeValuations A+
          (ProbePhysical.primeValuations B-ProbePhysical.primeValuations A)) := by
        rw [add_tsub_cancel_of_le h]
      _ = _ := by rw [ProbePhysical.idealFromValuations_add,
        ProbePhysical.idealFromValuations_primeValuations A hA]

lemma PairCubeFree_iff_prime_cube_not_dvd (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    PairCubeFree I J ↔ ∀ P : PrimeIdeal, ¬P.val^3 ∣ I*J := by
  unfold PairCubeFree
  have he (P : PrimeIdeal) : P.val^3 ∣ I*J ↔
      3 ≤ ProbePhysical.primeValuations I P+ProbePhysical.primeValuations J P := by
    rw [ideal_dvd_iff_valuations_le _ _ (pow_ne_zero _ P.property.ne_zero) (mul_ne_zero hI hJ),
      ProbePhysical.primeValuations_pow,ProbePhysical.primeValuations_prime,
      ProbePhysical.primeValuations_mul I J hI hJ]
    constructor
    · intro h
      have hh := h P
      simpa using hh
    · intro h Q
      by_cases hQ : Q=P
      · subst Q; simpa using h
      · simp [hQ]
  simp_rw [he]
  exact forall_congr' (fun P => by omega)

theorem correctedPairEulerCoefficient_eq (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    correctedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J =
      if PairAllowed bad allowed I J then idealCoeff ψ₁ I*idealCoeff ψ₂ J else 0 := by
  rw [correctedPairEulerCoefficient_local χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂]
  by_cases h : PairAllowed bad allowed I J
  · rw [ite_eq_left h]
    have hg (P : PrimeIdeal) (hP : P ∈ pairPrimeSupport I J \ bad) :
        ProbePhysical.primeValuations I P+ProbePhysical.primeValuations J P ≤ 2 :=
      h.1 P (Finset.mem_sdiff.mp hP).2
    simp only [Finset.prod_congr rfl (fun P hP => ite_eq_left (hg P hP)),
      Finset.prod_congr rfl (fun P hP => ite_eq_left (h.2 P hP))]
    rw [←Finset.prod_union Finset.sdiff_disjoint,Finset.sdiff_union_self_eq_union,
      Finset.prod_mul_distrib]
    rw [idealCoeff_valuation_product ψ₁ I hI (pairPrimeSupport I J ∪ bad)
      (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left),
      idealCoeff_valuation_product ψ₂ J hJ (pairPrimeSupport I J ∪ bad)
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)]
  · rw [ite_eq_right h]
    rcases not_and_or.mp h with hg | hb
    · obtain ⟨P,hP⟩ := not_forall.mp hg
      have hn : P ∉ bad := by tauto
      have hc : ¬ProbePhysical.primeValuations I P+ProbePhysical.primeValuations J P ≤ 2 := by tauto
      have hm : P ∈ pairPrimeSupport I J := by
        by_contra hh
        obtain ⟨hi,hj⟩ := valuation_zero_outside_pairSupport I J P hh
        simp [hi,hj] at hc
      rw [Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hm,hn⟩) (ite_eq_right hc),zero_mul]
    · obtain ⟨P,hP⟩ := not_forall.mp hb
      have hm : P ∈ bad := by tauto
      have hn : (ProbePhysical.primeValuations I P,ProbePhysical.primeValuations J P) ∉ allowed P := by tauto
      rw [Finset.prod_eq_zero hm (ite_eq_right hn),mul_zero]

lemma residualPairs_coefficient_agreement (c d u v : ℂ) (keep₁ keep₂ : Bool)
    (hc : keep₁=true → c=u) (hd : keep₂=true → d=v)
    (q : ℕ×ℕ) (hq : q ∈ residualPairs keep₁ keep₂) : c^q.1*d^q.2=u^q.1*v^q.2 := by
  have hm := (Finset.mem_filter.mp hq).2
  have h₁ : c^q.1=u^q.1 := by
    rcases hm.2.1 with hk | hz
    · rw [hc hk]
    · rw [hz]; simp
  have h₂ : d^q.2=v^q.2 := by
    rcases hm.2.2 with hk | hz
    · rw [hd hk]
    · rw [hz]; simp
  rw [h₁,h₂]

/-- Primitive induction agrees with the original zero-extended row on
precisely the valuations retained by the exceptional mask. -/
lemma pairCoeff_eq_inducing_of_allowed (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) (h : PairAllowed bad allowed I J) :
    idealCoeff χ₁ I*idealCoeff χ₂ J=idealCoeff ψ₁ I*idealCoeff ψ₂ J := by
  let S := pairPrimeSupport I J ∪ bad
  have hsI : (ProbePhysical.primeValuations I).support ⊆ S :=
    Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hsJ : (ProbePhysical.primeValuations J).support ⊆ S :=
    Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  rw [←idealCoeff_valuation_product χ₁ I hI S hsI,←idealCoeff_valuation_product χ₂ J hJ S hsJ,
    ←idealCoeff_valuation_product ψ₁ I hI S hsI,←idealCoeff_valuation_product ψ₂ J hJ S hsJ,
    ←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  by_cases hb : P ∈ bad
  · exact hbad P hb _ (h.2 P hb)
  · rw [hχ₁ P hb,hχ₂ P hb]

theorem correctedPairEulerCoefficient_original (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    correctedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J =
      if PairAllowed bad allowed I J then idealCoeff χ₁ I*idealCoeff χ₂ J else 0 := by
  rw [correctedPairEulerCoefficient_eq χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ I J hI hJ]
  split_ifs with h
  · exact (pairCoeff_eq_inducing_of_allowed χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad I J hI hJ h).symm
  · rfl

#print axioms correctedPairEulerCoefficient_original
#print axioms PairCubeFree_iff_prime_cube_not_dvd
#print axioms correctedPairEulerCoefficient_eq
#print axioms goodPairEulerCoefficient_eq
#print axioms correctedPairEulerCoefficient_local
end
end QRH.Cycle092.SignedCenter
