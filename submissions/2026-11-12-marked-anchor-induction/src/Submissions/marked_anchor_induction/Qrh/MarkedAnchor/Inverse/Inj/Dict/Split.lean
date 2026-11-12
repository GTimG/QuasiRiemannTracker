/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReference{Tuples,
Products,Overlap}.lean` (Apache-2.0). Modified by Sil (2026-11-12): no `PairwiseDisjoint` lists; the
tuple sum runs over INJECTIVE tuples only, and the Assigned × Remaining split keeps an injective
assigned part `x` and an injective remaining part `y` that avoids the primes of `∏ x`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceArithmetic

/-!
# Inverse.Inj.Dict.Split — the injective Assigned × Remaining split

* `PiOK I j t`: the `Finset.pi` tuple `t` is injective and none of its entries divides `j`
  (this is the tuple domain of the injective residual layer, `Inj/Init/ResidualTuple`).
* `join_injective_iff`: a joined tuple `joinTuple x y` (prime entries) is injective iff `x` is
  injective and `remainingPi y` is `PiOK` for `j = assignedIdeal x`.
* `remainingResidualInj`: the baseline `remainingResidual` restricted to `PiOK` remaining tuples.
* **`original_selected_overlap_inj`**: the baseline `original_selected_overlap` for the injective
  tuple sum, without disjointness.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths
open DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- An injective `Finset.pi` tuple none of whose entries divides `j`. -/
def PiOK {ι : Type*} (I : Finset ι) (j : Ideal O) (t : ∀ i ∈ I, Ideal O) : Prop :=
  (∀ i (hi : i ∈ I) k (hk : k ∈ I), t i hi = t k hk → i = k) ∧ ∀ i (hi : i ∈ I), ¬ t i hi ∣ j

/-- Two prime ideals, one dividing the other, are equal. -/
theorem prime_dvd_prime_eq {P Q : Ideal O} (hP : Prime P) (hQ : Prime Q) (h : P ∣ Q) : P = Q :=
  associated_iff_eq.mp ((hP.dvd_prime_iff_associated hQ).mp h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem joinTuple_val_mem (L : ι → Finset (Ideal O)) (J : Finset ι) (x : Assigned L J)
    (y : Remaining L J) (i : ι) (h : i ∈ J) :
    (joinTuple L J x y i).val = (x ⟨i, h⟩).val :=
  congrArg Subtype.val (joinTuple_assigned L J x y ⟨i, h⟩)

omit [Fintype ι] in
theorem joinTuple_val_not_mem (L : ι → Finset (Ideal O)) (J : Finset ι) (x : Assigned L J)
    (y : Remaining L J) (i : ι) (h : i ∉ J) :
    (joinTuple L J x y i).val = (y ⟨i, h⟩).val :=
  congrArg Subtype.val (joinTuple_remaining L J x y ⟨i, h⟩)

theorem join_injective_iff (L : ι → Finset (Ideal O)) (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (x : Assigned L J) (y : Remaining L J) :
    Function.Injective (fun i => (joinTuple L J x y i).val) ↔
      Function.Injective (fun i : ↥J => (x i).val) ∧
        PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y) := by
  have hrem (i : ι) (hi : i ∈ Finset.univ \ J) :
      remainingPi L J y i hi = (joinTuple L J x y i).val :=
    (joinTuple_val_not_mem L J x y i (Finset.mem_sdiff.mp hi).2).symm
  constructor
  · intro h
    refine ⟨fun a b hab => Subtype.ext (h ?_), fun i hi k hk he => h ?_, fun i hi hd => ?_⟩
    · simp only [joinTuple_val_mem L J x y a.val a.property,
        joinTuple_val_mem L J x y b.val b.property]
      exact hab
    · simp only
      rw [← hrem i hi, ← hrem k hk]
      exact he
    · have hiJ := (Finset.mem_sdiff.mp hi).2
      have hpr : Prime (remainingPi L J y i hi) := hprime i _ (y ⟨i, hiJ⟩).property
      obtain ⟨k, -, hk⟩ := (hpr.dvd_finsetProd_iff (fun k : ↥J => (x k).val)).mp hd
      have he := prime_dvd_prime_eq hpr (hprime k.val _ (x k).property) hk
      have hik : i = k.val := by
        apply h
        simp only
        rw [← hrem i hi, joinTuple_val_mem L J x y k.val k.property]
        exact he
      exact hiJ (hik ▸ k.property)
  · rintro ⟨hx, hok, havoid⟩ a b hab
    simp only at hab
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · rw [joinTuple_val_mem L J x y a ha, joinTuple_val_mem L J x y b hb] at hab
      exact congrArg Subtype.val (hx hab)
    · exfalso
      have hb' : b ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩
      apply havoid b hb'
      rw [hrem b hb', ← hab, joinTuple_val_mem L J x y a ha]
      exact Finset.dvd_prod_of_mem (fun k : ↥J => (x k).val) (Finset.mem_univ (⟨a, ha⟩ : ↥J))
    · exfalso
      have ha' : a ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
      apply havoid a ha'
      rw [hrem a ha', hab, joinTuple_val_mem L J x y b hb]
      exact Finset.dvd_prod_of_mem (fun k : ↥J => (x k).val) (Finset.mem_univ (⟨b, hb⟩ : ↥J))
    · have ha' : a ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
      have hb' : b ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩
      apply hok a ha' b hb'
      rw [hrem a ha', hrem b hb']
      exact hab

/-- A `PiOK` remaining tuple is injective as a function on the remaining slots. -/
theorem remaining_injective_of_ok (L : ι → Finset (Ideal O)) (J : Finset ι) (j : Ideal O)
    (y : Remaining L J) (hok : PiOK (Finset.univ \ J) j (remainingPi L J y)) :
    Function.Injective (fun i : {i : ι // i ∉ J} => (y i).val) := by
  intro a b hab
  exact Subtype.ext (hok.1 a.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, a.property⟩)
    b.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, b.property⟩) hab)

theorem remaining_moebius_of_ok (L : ι → Finset (Ideal O)) (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (j : Ideal O) (y : Remaining L J)
    (hok : PiOK (Finset.univ \ J) j (remainingPi L J y)) :
    (moebius (remainingIdeal L J y) : ℂ) = (-1 : ℂ) ^ Fintype.card {i : ι // i ∉ J} := by
  let : ∀ i : {i : ι // i ∉ J}, ((y i).val).IsMaximal := fun i =>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal, Finset.card_univ] using prime_product_moebius
    (fun i => (y i).val) (fun i => hprime i.val _ (y i).property)
    (remaining_injective_of_ok L J j y hok) Finset.univ

theorem assigned_remaining_squarefree_inj (L : ι → Finset (Ideal O))
    (hprime : ∀ i, ∀ P ∈ L i, Prime P) (J : Finset ι) (x : Assigned L J) (y : Remaining L J)
    (hx : Function.Injective (fun i : ↥J => (x i).val))
    (hok : PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y)) :
    Squarefree (assignedIdeal L J x * remainingIdeal L J y) := by
  rw [← joinTuple_product]
  exact tuple_product_squarefree _ (fun i => hprime i _ (joinTuple L J x y i).property)
    ((join_injective_iff L hprime J x y).mpr ⟨hx, hok⟩)

/-- The baseline `remainingResidual` restricted to `PiOK` remaining tuples. -/
def remainingResidualInj (S : Finset (Ideal O)) (L : ι → Finset (Ideal O)) (J : Finset ι)
    (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  ∑ y : Remaining L J, if PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y) then
    star ((∏ i : {i : ι // i ∉ J}, coeff i.val (y i).val) *
      (moebius (remainingIdeal L J y) : ℂ)) *
      conjugatedResidual S (assignedIdeal L J x * remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z G u
  else 0

/-- The injective assigned tuples on `J`. -/
def asgInj (L : ι → Finset (Ideal O)) (J : Finset ι) : Finset (Assigned L J) :=
  (Finset.univ : Finset (Assigned L J)).filter (fun x => Function.Injective (fun i : ↥J => (x i).val))

/-- The injective tuples. -/
def tupInj (L : ι → Finset (Ideal O)) : Finset (Tuple L) :=
  (Finset.univ : Finset (Tuple L)).filter (fun q => Function.Injective (fun i => (q i).val))

theorem original_selected_overlap_inj (S : Finset (Ideal O))
    (L : ι → Finset (Ideal O)) (hprime : ∀ i, ∀ P ∈ L i, Prime P) (coeff : ι → Ideal O → ℂ)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (G : Finset ι → ℝ)
    (hZ : 0 < Z) (u : O) :
    (∑ q ∈ tupInj L, (∏ i, coeff i (q i).val) *
      originalTotalPolynomial S (∏ i, (q i).val) η a W Z r z u) =
    ∑ J ∈ Finset.univ.powerset, ∑ x ∈ asgInj L J,
      (∏ i : ↥J, coeff i.val (x i).val) * (moebius (assignedIdeal L J x) : ℂ) *
      (Z^(-G J) : ℝ) * η (assignedIdeal L J x)^2 * (idealRowHom u (assignedIdeal L J x))^2 *
      star (remainingResidualInj S L J x coeff η a W Z r z (G J) u) := by
  unfold tupInj asgInj
  rw [Finset.sum_filter]
  calc
    _ = ∑ q : Tuple L, ∑ J ∈ Finset.univ.powerset,
        if Function.Injective (fun i => (q i).val) then (∏ i, coeff i (q i).val) *
          originalFixedPolynomial S (∏ i, (q i).val) (∏ i ∈ J, (q i).val) η a W Z r z u
        else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs with hq
      · rw [originalTotal_slot_subsets S _ (fun i => hprime i _ (q i).property) hq
          η a W Z r z hZ u, Finset.mul_sum]
      · simp
    _ = ∑ J ∈ Finset.univ.powerset, ∑ q : Tuple L,
        if Function.Injective (fun i => (q i).val) then (∏ i, coeff i (q i).val) *
          originalFixedPolynomial S (∏ i, (q i).val) (∏ i ∈ J, (q i).val) η a W Z r z u
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J _
      rw [sum_tuple_split L J, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Function.Injective (fun i : ↥J => (x i).val)
      · rw [if_pos hx]
        unfold remainingResidualInj
        rw [star_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hok : PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y)
        · rw [if_pos ((join_injective_iff L hprime J x y).mpr ⟨hx, hok⟩), if_pos hok]
          rw [joinTuple_coefficient_product, joinTuple_product, joinTuple_assigned_product,
            originalFixedPolynomial_eq_conjugatedResidual S
              (assigned_remaining_squarefree_inj L hprime J x y hx hok) (dvd_mul_right _ _) η a W hZ
              r z (G J),
            InverseInitialOverlap.residual, quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
          simp only [star_mul, star_star]
          ring
        · rw [if_neg (fun h => hok ((join_injective_iff L hprime J x y).mp h).2), if_neg hok,
            star_zero, mul_zero]
      · rw [if_neg hx]
        apply Finset.sum_eq_zero
        intro y _
        rw [if_neg (fun h => hx ((join_injective_iff L hprime J x y).mp h).1)]

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.original_selected_overlap_inj
