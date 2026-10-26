/- Eventual bounds over a finite family of ledgers with constants uniform over the family. Released under Apache 2.0.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Cycle63

open Filter

/-! The eventual bounds of Collet's step have the form `∃ degree S, ∀ x, ∃ C > 0, ∀ᶠ Z in atTop, P degree S x C Z`,
where `degree` is the degree of the height factor, `S` the set of the profile sources, `x` the data fixed before the
constant (the moduli of the family) and `C` the constant. A bound that holds for each member of a finite family of
ledgers, and that is monotone in the degree, the source set and the constant, holds for all members with one degree,
one source set and one constant: the largest degree, the union of the source sets and one plus the sum of the
constants, with the threshold of `Filter.eventually_all`. -/

/-- A family of eventual bounds over a finite index type, monotone in the degree, the source set and the constant,
holds uniformly over the index with one degree, one source set and one constant. -/
theorem eventually_uniform_of_finite {ι X : Type*} [Fintype ι] {P : ι → ℕ → Finset (ℕ × ℕ) → X → ℝ → ℝ → Prop}
    (hmono : ∀ i d d' S S' x C C' Z, d ≤ d' → S ⊆ S' → C ≤ C' → P i d S x C Z → P i d' S' x C' Z)
    (h : ∀ i, ∃ d : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z in atTop, P i d S x C Z) :
    ∃ d : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z in atTop, ∀ i, P i d S x C Z := by
  classical
  choose d S hS using h
  refine ⟨Finset.univ.sup d, Finset.univ.biUnion S, fun x => ?_⟩
  choose C hC hev using fun i => hS i x
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨1 + ∑ i, C i, by linarith, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hev] with Z hZ i
  have hCi : C i ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun j _ => (hC j).le) (Finset.mem_univ i)
    linarith
  exact hmono i (d i) _ (S i) _ x (C i) _ Z (Finset.le_sup (Finset.mem_univ i))
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)) hCi (hZ i)

end Cycle63
