/- Copyright (c) 2026 Sil. Apache-2.0.
The literal restricted ordinary pair and distinct marked primes produce a
fifth-power-free whole column. This connects restoration's restriction to
the actual Gauss fourth-power identity, with all nonunit cases retained.
-/
import Candidate.Feedback.FourthPower.KernelLabelledSlots
import Candidate.Feedback.FourthPower.GaussTransfer

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.KernelWholeColumns
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelIdeal KernelRestrictedState KernelLabelledSlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

variable {α : Type*} [Fintype α]

def markedProduct (slot : α → PrimeIdeal) : Id := ∏ i, (slot i).val

theorem markedProduct_ne_zero (slot : α → PrimeIdeal) : markedProduct slot ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (slot i).property.ne_zero)

theorem marked_valuation (slot : α → PrimeIdeal) (hinj : Function.Injective slot) (Q : Id) :
    valuation (markedProduct slot) Q = if ∃ i, (slot i).val=Q then 1 else 0 := by
  rw [markedProduct,valuation_prod _ _ (fun i _ => (slot i).property.ne_zero)]
  simp_rw [valuation_prime]
  by_cases h : ∃ i, (slot i).val=Q
  · obtain ⟨i,rfl⟩ := h
    rw [ite_eq_left ⟨i,rfl⟩,Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hn : (slot i).val ≠ (slot j).val := by
        intro he
        exact hji (hinj (Subtype.ext he).symm)
      simp [hn]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i _
    have hn : Q ≠ (slot i).val := fun he => h ⟨i,he.symm⟩
    simp [hn]

theorem restricted_whole_fifth_free (slot : α → PrimeIdeal) (hinj : Function.Injective slot)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hfree : SexticSieve.PowerFree 5 (I*J)) (havoid : ∀ i, ¬(slot i).val ∣ I*J) :
    SexticSieve.PowerFree 5 (I*J*markedProduct slot) := by
  have hIJ := mul_ne_zero hI hJ
  apply (powerFree_iff_valuations (mul_ne_zero hIJ (markedProduct_ne_zero slot))).mpr
  intro Q
  rw [valuation_mul hIJ (markedProduct_ne_zero slot),marked_valuation slot hinj Q]
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    have hz := (prime_not_dvd_iff (slot i) hIJ).mp (havoid i)
    rw [hi] at hz
    omega
  · simpa using (powerFree_iff_valuations hIJ).mp hfree Q

theorem labelled_restriction_whole (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hR : Restricted S (marked S slot) I J) :
    SexticSieve.PowerFree 5 (I*J*markedProduct (fun i => (slot i).val)) := by
  apply restricted_whole_fifth_free (fun i => (slot i).val)
    (fun i j h => hinj (Subtype.ext h)) hI hJ hR.1
  intro i
  exact hR.2 (slot i) ((marked_true S slot (slot i)).mpr ⟨i,rfl⟩)

omit [Fintype α] in
theorem element_fifth_free (a : O) (hf : SexticSieve.PowerFree 5 (Ideal.span {a})) :
    GaussTransfer.FifthFree a := by
  intro p hp hd
  have hprime : Prime (Ideal.span {p} : Id) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  apply hf (Ideal.span {p}) hprime
  obtain ⟨q,hq⟩ := hd
  refine ⟨Ideal.span {q},?_⟩
  rw [Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton,hq]

/-- Direct application of the already proved nonunit-safe Gauss transfer to
the complete ordinary-plus-marked column, without discarding marked factors. -/
theorem restricted_gauss_transfer (slot : α → PrimeIdeal) (hinj : Function.Injective slot)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hfree : SexticSieve.PowerFree 5 (I*J)) (havoid : ∀ i, ¬(slot i).val ∣ I*J)
    (a : O) (ha : Supported (Ideal.span {a}))
    (hspan : Ideal.span {a}=I*J*markedProduct slot) (D k : O) :
    CenteredMomentGaussEnergy.gaussRow a ha (D^4*k) =
      (idealRowHom D (Ideal.span {a}))^2*CenteredMomentGaussEnergy.gaussRow a ha k := by
  apply GaussTransfer.normalized_fourth_power a ha
  apply element_fifth_free
  rw [hspan]
  exact restricted_whole_fifth_free slot hinj hI hJ hfree havoid

end
end Candidate.Feedback.FourthPower.KernelWholeColumns
