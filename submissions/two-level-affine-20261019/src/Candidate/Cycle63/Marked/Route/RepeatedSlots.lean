import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Finite decoupling of repeated prime slots.  This file develops the finite
algebra needed to extend a uniform disjoint-pool moment estimate.  It does not
assert a nonvanishing theorem.
-/

noncomputable section
open scoped BigOperators Classical

namespace RepeatedPrimeSlots

variable {A I : Type*} [Fintype A] [Fintype I]

/-- A coloring which gives every member of a tuple its prescribed slot color. -/
def Compatible (x : I → A) (c : A → I) : Prop := ∀ i, c (x i) = i

omit [Fintype A] [Fintype I] in
theorem compatible_injective {x : I → A} {c : A → I}
    (h : Compatible x c) : Function.Injective x := by
  intro i j hij
  calc i = c (x i) := (h i).symm
       _ = c (x j) := congrArg c hij
       _ = j := h j

/-- Once colors on an injective tuple are fixed, all other colors are free. -/
def compatibleEquiv (x : I → A) (hx : Function.Injective x) :
    {c : A → I // Compatible x c} ≃ ({a : A // a ∉ Set.range x} → I) := by
  classical
  let extend (f : {a : A // a ∉ Set.range x} → I) : A → I :=
    fun a => if h : a ∈ Set.range x then Classical.choose h else f ⟨a,h⟩
  have extend_on (f : {a : A // a ∉ Set.range x} → I) (i : I) :
      extend f (x i) = i := by
    dsimp [extend]
    rw [dite_eq_left (Set.mem_range_self i)]
    exact hx (Classical.choose_spec (Set.mem_range_self i))
  refine {
    toFun := fun c a => c.val a.val
    invFun := fun f => ⟨extend f, extend_on f⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro c
    apply Subtype.ext
    funext a
    change extend (fun a => c.val a.val) a = c.val a
    by_cases h : a ∈ Set.range x
    · obtain ⟨i,rfl⟩ := h
      exact (extend_on (fun a => c.val a.val) i).trans (c.property i).symm
    · dsimp only [extend]
      rw [dite_eq_right h]
  · intro f
    funext a
    change extend f a.val = f a
    dsimp only [extend]
    rw [dite_eq_right a.property]

theorem card_compatible (x : I → A) (hx : Function.Injective x) :
    Fintype.card {c : A → I // Compatible x c} =
      Fintype.card I ^ (Fintype.card A - Fintype.card I) := by
  classical
  rw [Fintype.card_congr (compatibleEquiv x hx), Fintype.card_fun]
  congr 1
  change Fintype.card (↥(Set.range x)ᶜ) = _
  rw [Fintype.card_compl_set]
  congr 1
  exact Fintype.card_congr (Equiv.ofInjective x hx).symm

theorem card_compatible_of_not_injective (x : I → A) (hx : ¬Function.Injective x) :
    Fintype.card {c : A → I // Compatible x c} = 0 := by
  classical
  let : IsEmpty {c : A → I // Compatible x c} :=
    ⟨fun c => hx (compatible_injective c.property)⟩
  exact Fintype.card_eq_zero

/-- Unnormalized finite coloring identity.  The size of the prime universe
occurs only in the common number of extensions of an injective tuple. -/
theorem sum_colored_products {R : Type*} [CommSemiring R] (a : I → A → R) :
    (∑ c : A → I, ∏ i, ∑ p : A, if c p = i then a i p else 0) =
      (Fintype.card I ^ (Fintype.card A - Fintype.card I) : ℕ) *
        ∑ x : I → A, if Function.Injective x then ∏ i, a i (x i) else 0 := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  simp_rw [Fintype.prod_ite_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun c : A → I => ∀ i, c (x i) = i)).card =
      Fintype.card {c : A → I // Compatible x c} := by
    symm
    apply Fintype.card_of_subtype
    intro c
    simp [Compatible]
  rw [hc]
  by_cases hx : Function.Injective x
  · rw [ite_eq_left hx, card_compatible x hx]
  · rw [ite_eq_right hx, card_compatible_of_not_injective x hx]
    simp

end RepeatedPrimeSlots
