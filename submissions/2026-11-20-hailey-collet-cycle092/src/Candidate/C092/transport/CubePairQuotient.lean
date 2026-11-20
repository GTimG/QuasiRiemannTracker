/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairMask

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

lemma primeValuations_prod {α : Type*} (S : Finset α) (f : α → Ideal O)
    (hn : ∀ i ∈ S,f i ≠ 0) :
    ProbePhysical.primeValuations (∏ i ∈ S,f i)=∑ i ∈ S,ProbePhysical.primeValuations (f i) := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,ProbePhysical.primeValuations_one]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,ProbePhysical.primeValuations_mul]
    · rw [ih (fun j hj => hn j (Finset.mem_insert_of_mem hj))]
    · exact hn i (Finset.mem_insert_self _ _)
    · exact Finset.prod_ne_zero_iff.mpr (fun j hj => hn j (Finset.mem_insert_of_mem hj))

lemma valuation_prime_product {α : Type*} [Fintype α] (p : α → PrimeIdeal) (n : α → ℕ)
    (P : PrimeIdeal) :
    ProbePhysical.primeValuations (∏ i,(p i).val ^ n i) P=
      ∑ i,if p i=P then n i else 0 := by
  rw [primeValuations_prod Finset.univ _ (fun i _ => pow_ne_zero _ (p i).property.ne_zero)]
  simp only [Finsupp.finsetSum_apply,ProbePhysical.primeValuations_pow,ProbePhysical.primeValuations_prime,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i=P
  · simp [h]
  · simp [h,Ne.symm h]

lemma valuation_prime_product_at {α : Type*} [Fintype α] (p : α → PrimeIdeal)
    (hp : Function.Injective p) (n : α → ℕ) (i : α) :
    ProbePhysical.primeValuations (∏ j,(p j).val ^ n j) (p i)=n i := by
  rw [valuation_prime_product]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (hp h))]
  · simp

lemma valuation_prime_product_outside {α : Type*} [Fintype α] (p : α → PrimeIdeal)
    (n : α → ℕ) (P : PrimeIdeal) (h : P ∉ Set.range p) :
    ProbePhysical.primeValuations (∏ j,(p j).val ^ n j) P=0 := by
  rw [valuation_prime_product]
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun he => h ⟨i,he⟩)

lemma correctedIdeal₁_valuation (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed) (P : PrimeIdeal) :
    ProbePhysical.primeValuations (correctedIdeal₁ bad allowed k) P=
      (∑ Q : bad,if Q.val=P then deletionExponent₁ (k.1 Q)+(k.2.1 Q).val.1 else 0)+
      ∑ Q : k.2.2.1,if Q.val.val=P then (h3Exponent (k.2.2.2 Q)).1 else 0 := by
  rw [correctedIdeal₁,ProbePhysical.primeValuations_mul _ _ (deletionIdeal₁_ne_zero bad k.1)
      (fullIdeal₁_ne_zero bad allowed k.2),fullIdeal₁,
    ProbePhysical.primeValuations_mul _ _ (badIdeal₁_ne_zero bad allowed k.2.1)
      (goodIdeal₁_ne_zero bad k.2.2)]
  simp only [Finsupp.add_apply,deletionIdeal₁,badIdeal₁,goodIdeal₁]
  rw [valuation_prime_product,valuation_prime_product,valuation_prime_product,←add_assoc,←Finset.sum_add_distrib]
  apply congrArg (fun z : ℕ => z+_)
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs <;> simp

lemma correctedIdeal₂_valuation (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed) (P : PrimeIdeal) :
    ProbePhysical.primeValuations (correctedIdeal₂ bad allowed k) P=
      (∑ Q : bad,if Q.val=P then deletionExponent₂ (k.1 Q)+(k.2.1 Q).val.2 else 0)+
      ∑ Q : k.2.2.1,if Q.val.val=P then (h3Exponent (k.2.2.2 Q)).2 else 0 := by
  rw [correctedIdeal₂,ProbePhysical.primeValuations_mul _ _ (deletionIdeal₂_ne_zero bad k.1)
      (fullIdeal₂_ne_zero bad allowed k.2),fullIdeal₂,
    ProbePhysical.primeValuations_mul _ _ (badIdeal₂_ne_zero bad allowed k.2.1)
      (goodIdeal₂_ne_zero bad k.2.2)]
  simp only [Finsupp.add_apply,deletionIdeal₂,badIdeal₂,goodIdeal₂]
  rw [valuation_prime_product,valuation_prime_product,valuation_prime_product,←add_assoc,←Finset.sum_add_distrib]
  apply congrArg (fun z : ℕ => z+_)
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs <;> simp

def numeratorValuation (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad))
    (m : bad → ℕ) (n : S → ℕ) (P : PrimeIdeal) : ℕ :=
  (∑ Q : bad,if Q.val=P then m Q else 0)+∑ Q : S,if Q.val.val=P then n Q else 0

lemma sum_ite_injective_at {α β : Type*} [Fintype α] [DecidableEq β] (p : α → β)
    (hp : Function.Injective p) (n : α → ℕ) (i : α) :
    (∑ j,if p j=p i then n j else 0)=n i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact ite_eq_right (fun h => hj (hp h))
  · simp

lemma numeratorValuation_bad (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad))
    (m : bad → ℕ) (n : S → ℕ) (P : bad) : numeratorValuation bad S m n P.val=m P := by
  unfold numeratorValuation
  rw [sum_ite_injective_at Subtype.val Subtype.val_injective]
  have hh (Q : S) : Q.val.val ≠ P.val := by
    intro he
    exact Q.val.property (he ▸ P.property)
  simp only [ite_eq_right (hh _),Finset.sum_const_zero,add_zero]

lemma numeratorValuation_good (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad))
    (m : bad → ℕ) (n : S → ℕ) (P : S) : numeratorValuation bad S m n P.val.val=n P := by
  unfold numeratorValuation
  have hh (Q : bad) : Q.val ≠ P.val.val := by
    intro he
    exact P.val.property (he ▸ Q.property)
  simp only [ite_eq_right (hh _),Finset.sum_const_zero,zero_add]
  exact sum_ite_injective_at (fun Q : S => Q.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) n P

lemma numeratorValuation_outside (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad))
    (m : bad → ℕ) (n : S → ℕ) (P : PrimeIdeal) (hP : P ∉ bad)
    (hS : (⟨P,hP⟩ : GoodPrimes bad) ∉ S) : numeratorValuation bad S m n P=0 := by
  unfold numeratorValuation
  have hb (Q : bad) : Q.val ≠ P := by intro he; exact hP (he ▸ Q.property)
  have hg (Q : S) : Q.val.val ≠ P := by
    intro he
    exact hS ((Subtype.ext he : Q.val=⟨P,hP⟩) ▸ Q.property)
  simp only [ite_eq_right (hb _),ite_eq_right (hg _),Finset.sum_const_zero,zero_add]

lemma numeratorValuation_le_iff (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad))
    (m : bad → ℕ) (n : S → ℕ) (a : PrimeIdeal → ℕ) :
    (∀ P,numeratorValuation bad S m n P ≤ a P) ↔
      (∀ P : bad,m P ≤ a P.val) ∧ (∀ P : S,n P ≤ a P.val.val) := by
  constructor
  · intro h
    exact ⟨fun P => (numeratorValuation_bad bad S m n P) ▸ h P.val,
      fun P => (numeratorValuation_good bad S m n P) ▸ h P.val.val⟩
  · rintro ⟨hb,hg⟩ P
    by_cases hp : P ∈ bad
    · rw [numeratorValuation_bad bad S m n ⟨P,hp⟩]
      exact hb ⟨P,hp⟩
    · by_cases hs : (⟨P,hp⟩ : GoodPrimes bad) ∈ S
      · rw [numeratorValuation_good bad S m n ⟨⟨P,hp⟩,hs⟩]
        exact hg ⟨⟨P,hp⟩,hs⟩
      · rw [numeratorValuation_outside bad S m n P hp hs]
        exact Nat.zero_le _

def CorrectedAdmissible (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (a b : PrimeIdeal → ℕ) (k : CorrectedIndex bad allowed) : Prop :=
  (∀ P : bad,(k.2.1 P).val.1+deletionExponent₁ (k.1 P) ≤ a P.val ∧
    (k.2.1 P).val.2+deletionExponent₂ (k.1 P) ≤ b P.val) ∧
  (∀ P : k.2.2.1,(h3Exponent (k.2.2.2 P)).1 ≤ a P.val.val ∧
    (h3Exponent (k.2.2.2 P)).2 ≤ b P.val.val)

theorem correctedIdeal_dvd_iff_admissible (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (correctedIdeal₁ bad allowed k ∣ I ∧ correctedIdeal₂ bad allowed k ∣ J) ↔
      CorrectedAdmissible bad allowed (ProbePhysical.primeValuations I) (ProbePhysical.primeValuations J) k := by
  rw [ideal_dvd_iff_valuations_le _ _ (correctedIdeal₁_ne_zero bad allowed k) hI,
    ideal_dvd_iff_valuations_le _ _ (correctedIdeal₂_ne_zero bad allowed k) hJ]
  change ((∀ P,ProbePhysical.primeValuations (correctedIdeal₁ bad allowed k) P ≤ _) ∧
    (∀ P,ProbePhysical.primeValuations (correctedIdeal₂ bad allowed k) P ≤ _)) ↔ _
  simp_rw [correctedIdeal₁_valuation,correctedIdeal₂_valuation]
  change ((∀ P,numeratorValuation bad k.2.2.1 _ _ P ≤ _) ∧
    (∀ P,numeratorValuation bad k.2.2.1 _ _ P ≤ _)) ↔ _
  rw [numeratorValuation_le_iff,numeratorValuation_le_iff]
  unfold CorrectedAdmissible
  simp only [Nat.add_comm,forall_and]
  tauto

lemma admissible_good_support (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed) (I J : Ideal O)
    (h : CorrectedAdmissible bad allowed (ProbePhysical.primeValuations I)
      (ProbePhysical.primeValuations J) k) : k.2.2.1 ⊆ goodPairSupport bad I J := by
  intro P hP
  have hh := h.2 ⟨P,hP⟩
  have hm : P.val ∈ pairPrimeSupport I J := by
    by_contra hn
    obtain ⟨hi,hj⟩ := valuation_zero_outside_pairSupport I J P.val hn
    have hd := h3Exponent_degree (k.2.2.2 ⟨P,hP⟩)
    simp only [hi,hj] at hh
    omega
  simpa only [goodPairSupport,Finset.mem_subtype] using hm

#print axioms correctedIdeal_dvd_iff_admissible
#print axioms admissible_good_support
#print axioms correctedIdeal₁_valuation
#print axioms correctedIdeal₂_valuation
end
end QRH.Cycle092.SignedCenter
