/- Copyright (c) 2026 Sil. Apache-2.0.
The literal fifth-free and marked-prime restriction under genuine complete
common extraction. Extracted and residual ordinary parts are coprime;
frozen marked primes constrain the extracted part, live ones the residual.
This identity does not erase shifted thresholds in artificial allocations.
-/
import Candidate.FourthPower.MixedActualColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum

set_option autoImplicit false
namespace Candidate.FourthPower.MixedCommonRestriction
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelIdeal KernelRestrictedState KernelLabelledSlots KernelPunctureRows
open KernelWholeColumns
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem power_free_coprime (A B : Id) (hA : A≠0) (hB : B≠0) (hc : IsCoprime A B) :
    SexticSieve.PowerFree 5 (A*B) ↔ SexticSieve.PowerFree 5 A ∧ SexticSieve.PowerFree 5 B := by
  rw [powerFree_iff_valuations (mul_ne_zero hA hB),powerFree_iff_valuations hA,
    powerFree_iff_valuations hB]
  simp_rw [valuation_mul hA hB]
  constructor
  · intro h
    exact ⟨fun P=>by have := h P;omega,fun P=>by have := h P;omega⟩
  · rintro ⟨ha,hb⟩ P
    have hd := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hA hB).mpr hc
    by_cases hp : P∈primeSupport A
    · have hn : P∉primeSupport B := fun hh=>Finset.disjoint_left.mp hd hp hh
      rw [valuation_eq_zero_of_not_mem hn,add_zero]
      exact ha P
    · rw [valuation_eq_zero_of_not_mem hp,zero_add]
      exact hb P

/-- H is a common ordinary puncture, M is the complete marked product. -/
def restriction (H M I J : Id) : Prop :=
  SexticSieve.PowerFree 5 (I*J) ∧ IsCoprime (H*M) (I*J)

def punctureProduct (S H : Finset PrimeIdeal) : Id := ∏P∈S.filter (fun P=>P∈H),P.val

theorem prime_coprime (P : PrimeIdeal) (I : Id) : IsCoprime P.val I ↔ ¬P.val∣I := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem labelled_restriction {α : Type*} [Fintype α]
    (S H : Finset PrimeIdeal) (slot : α→S) (I J : Id) :
    Restricted S (augmented S H (marked S slot)) I J ↔
      restriction (punctureProduct S H) (markedProduct (fun i=>(slot i).val)) I J := by
  rw [augmented_restriction]
  unfold Restricted restriction
  rw [IsCoprime.mul_left_iff]
  have hh : IsCoprime (punctureProduct S H) (I*J) ↔
      ∀P : S,P.val∈H→¬P.val.val∣I*J := by
    simp only [punctureProduct,IsCoprime.prod_left_iff,Finset.mem_filter,prime_coprime]
    constructor
    · intro h P hp
      exact h P.val ⟨P.property,hp⟩
    · intro h P hp
      exact h ⟨P,hp.1⟩ hp.2
  have hm : IsCoprime (markedProduct (fun i=>(slot i).val)) (I*J) ↔
      ∀P : S,marked S slot P=true→¬P.val.val∣I*J := by
    simp only [markedProduct,IsCoprime.prod_left_iff,Finset.mem_univ,forall_const,prime_coprime]
    constructor
    · intro h P hp
      obtain ⟨i,rfl⟩ := (marked_true S slot P).mp hp
      exact h i
    · intro h i
      exact h (slot i) ((marked_true S slot (slot i)).mpr ⟨i,rfl⟩)
  rw [hh,hm]
  tauto

theorem restriction_split (H F L B₁ B₂ I₁ I₂ : Id)
    (hB : B₁*B₂≠0) (hI : I₁*I₂≠0)
    (hc : IsCoprime (B₁*B₂) (I₁*I₂))
    (hF : IsCoprime F (I₁*I₂)) (hL : IsCoprime L (B₁*B₂)) :
    restriction H (F*L) (B₁*I₁) (B₂*I₂) ↔
      restriction H F B₁ B₂ ∧ restriction H L I₁ I₂ := by
  have he : (B₁*I₁)*(B₂*I₂)=(B₁*B₂)*(I₁*I₂) := by ring
  simp only [restriction,he,power_free_coprime _ _ hB hI hc,
    IsCoprime.mul_left_iff,IsCoprime.mul_right_iff] at hF hL ⊢
  tauto

/-- Coprimality against the entire genuine common support supplies all
cross conditions, not an assumption on the polynomial coefficients. -/
theorem restriction_split_common (H C F L B₁ B₂ I₁ I₂ : Id)
    (hB : B₁*B₂≠0) (hI : I₁*I₂≠0)
    (hBC : B₁*B₂∣C) (hFC : F∣C)
    (hCI : IsCoprime C (I₁*I₂)) (hCL : IsCoprime C L) :
    restriction H (F*L) (B₁*I₁) (B₂*I₂) ↔
      restriction H F B₁ B₂ ∧ restriction H L I₁ I₂ :=
  restriction_split H F L B₁ B₂ I₁ I₂ hB hI
    (hCI.of_isCoprime_of_dvd_left hBC) (hCI.of_isCoprime_of_dvd_left hFC)
    (hCL.of_isCoprime_of_dvd_left hBC).symm

def restrictionWeight (H M I J : Id) : ℂ := if restriction H M I J then 1 else 0

theorem restriction_weight_split (H C F L B₁ B₂ I₁ I₂ : Id)
    (hB : B₁*B₂≠0) (hI : I₁*I₂≠0)
    (hBC : B₁*B₂∣C) (hFC : F∣C)
    (hCI : IsCoprime C (I₁*I₂)) (hCL : IsCoprime C L) :
    restrictionWeight H (F*L) (B₁*I₁) (B₂*I₂)=
      restrictionWeight H F B₁ B₂*restrictionWeight H L I₁ I₂ := by
  unfold restrictionWeight
  rw [restriction_split_common H C F L B₁ B₂ I₁ I₂ hB hI hBC hFC hCI hCL]
  split_ifs <;> simp_all

end
end Candidate.FourthPower.MixedCommonRestriction
