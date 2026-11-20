/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairQuotient

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

def idealQuotient (I D : Ideal O) : Ideal O :=
  ProbePhysical.idealFromValuations (ProbePhysical.primeValuations I-ProbePhysical.primeValuations D)

lemma idealQuotient_mul (I D : Ideal O) (hI : I ≠ 0) (hD : D ≠ 0) (hd : D ∣ I) :
    D*idealQuotient I D=I := by
  rw [ideal_dvd_iff_valuations_le D I hD hI] at hd
  unfold idealQuotient
  conv_lhs => lhs; rw [←ProbePhysical.idealFromValuations_primeValuations D hD]
  rw [←ProbePhysical.idealFromValuations_add,add_tsub_cancel_of_le hd,
    ProbePhysical.idealFromValuations_primeValuations I hI]

lemma idealQuotient_mul_cancel (D A : Ideal O) (hD : D ≠ 0) (hA : A ≠ 0) :
    idealQuotient (D*A) D=A := by
  unfold idealQuotient
  rw [ProbePhysical.primeValuations_mul D A hD hA,add_tsub_cancel_left,
    ProbePhysical.idealFromValuations_primeValuations A hA]

lemma idealCoeff_quotient_product (χ : Character) (I D : Ideal O) (S : Finset PrimeIdeal)
    (hS : (ProbePhysical.primeValuations I).support ⊆ S) :
    idealCoeff χ (idealQuotient I D)=
      ∏ P ∈ S,(idealCoeff χ P.val)^(ProbePhysical.primeValuations I P-ProbePhysical.primeValuations D P) := by
  have hs : (ProbePhysical.primeValuations (idealQuotient I D)).support ⊆ S := by
    simpa only [idealQuotient,ProbePhysical.primeValuations_idealFromValuations] using
      (Finsupp.support_tsub.trans hS)
  rw [←idealCoeff_valuation_product χ (idealQuotient I D)
    (ProbePhysical.idealFromValuations_ne_zero _) S hs]
  simp only [idealQuotient,ProbePhysical.primeValuations_idealFromValuations,Finsupp.tsub_apply]

lemma prod_partition_bad (U bad : Finset PrimeIdeal) (f : PrimeIdeal → ℂ) :
    (∏ P ∈ U ∪ bad,f P)=(∏ P : bad,f P.val)*(∏ P ∈ U \ bad,f P) := by
  rw [←Finset.sdiff_union_self_eq_union,Finset.prod_union Finset.sdiff_disjoint,
    mul_comm,Finset.prod_coe_sort]

def coordinateResidual (χ : Character) (bad : Finset PrimeIdeal) (S T : Finset (GoodPrimes bad))
    (a : PrimeIdeal → ℕ) (m : bad → ℕ) (n : T → ℕ) : ℂ :=
  (∏ P : bad,(idealCoeff χ P.val.val)^(a P.val-m P))*
    ((∏ P : T,(idealCoeff χ P.val.val.val)^(a P.val.val-n P))*
      ∏ P ∈ S \ T,(idealCoeff χ P.val)^(a P.val))

lemma coordinateResidual_eq_quotient (χ : Character) (I J D : Ideal O)
    (bad : Finset PrimeIdeal) (T : Finset (GoodPrimes bad)) (m : bad → ℕ) (n : T → ℕ)
    (hT : T ⊆ goodPairSupport bad I J)
    (hv : ∀ P,ProbePhysical.primeValuations D P=numeratorValuation bad T m n P) :
    coordinateResidual χ bad (goodPairSupport bad I J) T (ProbePhysical.primeValuations I) m n=
      idealCoeff χ (idealQuotient I D) := by
  rw [idealCoeff_quotient_product χ I D (pairPrimeSupport I J ∪ bad)
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left),prod_partition_bad]
  rw [←prod_goodPairSupport bad I J (fun P =>
    (idealCoeff χ P.val)^(ProbePhysical.primeValuations I P-ProbePhysical.primeValuations D P))]
  unfold coordinateResidual
  apply congrArg₂ (fun x y : ℂ => x*y)
  · apply Finset.prod_congr rfl
    intro P _
    rw [hv P.val,numeratorValuation_bad]
  · rw [←Finset.prod_sdiff hT]
    conv_rhs => rw [mul_comm]
    rw [←Finset.prod_coe_sort T]
    apply congrArg₂ (fun x y : ℂ => x*y)
    · apply Finset.prod_congr rfl
      intro P _
      rw [hv P.val.val,numeratorValuation_good]
    · apply Finset.prod_congr rfl
      intro P hP
      rw [hv P.val,numeratorValuation_outside bad T m n P.val P.property (Finset.mem_sdiff.mp hP).2,
        Nat.sub_zero]

lemma correctedResidualKernel_zero (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed)
    (h : ¬CorrectedAdmissible bad allowed a b k) :
    correctedResidualKernel χ₁ χ₂ bad allowed a b S k=0 := by
  rcases not_and_or.mp h with hb | hg
  · obtain ⟨P,hP⟩ := not_forall.mp hb
    have hz : ordinaryResidualLocal χ₁ χ₂ a b P.val
        ((k.2.1 P).val.1+deletionExponent₁ (k.1 P))
        ((k.2.1 P).val.2+deletionExponent₂ (k.1 P))=0 := ite_eq_right hP
    rw [correctedResidualKernel,badResidualKernel,
      Finset.prod_eq_zero (Finset.mem_univ P) hz,zero_mul]
  · obtain ⟨P,hP⟩ := not_forall.mp hg
    have hz : ordinaryResidualLocal χ₁ χ₂ a b P.val.val
        (h3Exponent (k.2.2.2 P)).1 (h3Exponent (k.2.2.2 P)).2=0 := ite_eq_right hP
    rw [correctedResidualKernel,goodResidualKernel,
      Finset.prod_eq_zero (Finset.mem_univ P) hz,zero_mul,mul_zero]

lemma correctedResidualKernel_of_admissible (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed)
    (h : CorrectedAdmissible bad allowed a b k) :
    correctedResidualKernel χ₁ χ₂ bad allowed a b S k=
      coordinateResidual χ₁ bad S k.2.2.1 a
        (fun P => (k.2.1 P).val.1+deletionExponent₁ (k.1 P))
        (fun P => (h3Exponent (k.2.2.2 P)).1)*
      coordinateResidual χ₂ bad S k.2.2.1 b
        (fun P => (k.2.1 P).val.2+deletionExponent₂ (k.1 P))
        (fun P => (h3Exponent (k.2.2.2 P)).2) := by
  unfold correctedResidualKernel badResidualKernel goodResidualKernel
  have hb (P : bad) : ordinaryResidualLocal χ₁ χ₂ a b P.val
      ((k.2.1 P).val.1+deletionExponent₁ (k.1 P))
      ((k.2.1 P).val.2+deletionExponent₂ (k.1 P))=
      (idealCoeff χ₁ P.val.val)^(a P.val-((k.2.1 P).val.1+deletionExponent₁ (k.1 P)))*
      (idealCoeff χ₂ P.val.val)^(b P.val-((k.2.1 P).val.2+deletionExponent₂ (k.1 P))) :=
    ite_eq_left (h.1 P)
  have hg (P : k.2.2.1) : ordinaryResidualLocal χ₁ χ₂ a b P.val.val
      (h3Exponent (k.2.2.2 P)).1 (h3Exponent (k.2.2.2 P)).2=
      (idealCoeff χ₁ P.val.val.val)^(a P.val.val-(h3Exponent (k.2.2.2 P)).1)*
      (idealCoeff χ₂ P.val.val.val)^(b P.val.val-(h3Exponent (k.2.2.2 P)).2) :=
    ite_eq_left (h.2 P)
  simp_rw [hb,hg]
  simp only [coordinateResidual,ordinaryLocalCoefficient,Finset.prod_mul_distrib]
  ring

theorem correctedResidualKernel_eq_quotient (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hT : k.2.2.1 ⊆ goodPairSupport bad I J) :
    correctedResidualKernel χ₁ χ₂ bad allowed (ProbePhysical.primeValuations I)
      (ProbePhysical.primeValuations J) (goodPairSupport bad I J) k=
    if correctedIdeal₁ bad allowed k ∣ I ∧ correctedIdeal₂ bad allowed k ∣ J then
      idealCoeff χ₁ (idealQuotient I (correctedIdeal₁ bad allowed k))*
        idealCoeff χ₂ (idealQuotient J (correctedIdeal₂ bad allowed k)) else 0 := by
  by_cases hd : correctedIdeal₁ bad allowed k ∣ I ∧ correctedIdeal₂ bad allowed k ∣ J
  · rw [ite_eq_left hd,correctedResidualKernel_of_admissible χ₁ χ₂ bad allowed _ _ _ k
      ((correctedIdeal_dvd_iff_admissible bad allowed k I J hI hJ).mp hd)]
    apply congrArg₂ (fun x y : ℂ => x*y)
    · apply coordinateResidual_eq_quotient χ₁ I J _ bad k.2.2.1 _ _ hT
      intro P
      rw [correctedIdeal₁_valuation]
      unfold numeratorValuation
      apply congrArg (fun z : ℕ => z+_)
      apply Finset.sum_congr rfl
      intro Q _
      split_ifs <;> dsimp only <;> omega
    · have hs : goodPairSupport bad I J=goodPairSupport bad J I := by
        unfold goodPairSupport pairPrimeSupport
        rw [Finset.union_comm]
      rw [hs]
      apply coordinateResidual_eq_quotient χ₂ J I _ bad k.2.2.1 _ _ (hs ▸ hT)
      intro P
      rw [correctedIdeal₂_valuation]
      unfold numeratorValuation
      apply congrArg (fun z : ℕ => z+_)
      apply Finset.sum_congr rfl
      intro Q _
      split_ifs <;> dsimp only <;> omega
  · rw [ite_eq_right hd]
    apply correctedResidualKernel_zero
    exact fun h => hd ((correctedIdeal_dvd_iff_admissible bad allowed k I J hI hJ).mpr h)

#print axioms correctedResidualKernel_eq_quotient
#print axioms coordinateResidual_eq_quotient
end
end QRH.Cycle092.SignedCenter
