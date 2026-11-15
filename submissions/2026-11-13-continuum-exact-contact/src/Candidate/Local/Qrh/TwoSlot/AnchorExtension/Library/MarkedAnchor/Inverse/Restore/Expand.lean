/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Euler
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.Marks

/-!
# Inverse.Restore.Expand — tuple expansion of a marked profiled column (generic)

For a multiplicative prime weight `c`, norms `n`, a profile `Φ` and slot lists that are pairwise
disjoint on the slots, the marked column
`markedCol = ∑_{A ⊆ pool} (∏_A c) · primeMark slots lists a A · Φ(∏_A n / X)`
is a sum over tuples `d ∈ slots.pi lists` (one required prime per slot) of the tuple coefficient
`∏_i a_i(d_i) c(d_i)` times the UNMARKED column on `pool \ img d` at the scale `X / ∏_i n(d_i)`
(terms with `img d ⊄ pool` vanish):

* `markedCol_tuple`.

Together with `Euler.col_avoid_finite` (put the primes of `img d` back into the column) this is
the reciprocal Euler factor of the required slot primes.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped BigOperators
open OAI.SevenEighths.InverseMoment

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

/-- The marked profiled column. -/
def markedCol (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (pool : Finset ι) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) : ℂ :=
  ∑ A ∈ pool.powerset, (∏ i ∈ A, c i) * primeMark slots lists a A * Φ ((∏ i ∈ A, n i) / X)

/-- The image of a tuple. -/
def tupleImg (slots : Finset σ) (d : ∀ i ∈ slots, ι) : Finset ι :=
  slots.attach.image (fun i => d i.1 i.2)

theorem mem_tupleImg {slots : Finset σ} {d : ∀ i ∈ slots, ι} {x : ι} :
    x ∈ tupleImg slots d ↔ ∃ i, ∃ hi : i ∈ slots, d i hi = x := by
  simp [tupleImg]

/-- Subsets of `pool` containing `S ⊆ pool` are `S ∪ A'`, `A' ⊆ pool \ S`. -/
theorem sum_powerset_superset {β : Type*} [AddCommMonoid β] (pool S : Finset ι) (hS : S ⊆ pool)
    (g : Finset ι → β) :
    ∑ A ∈ pool.powerset.filter (fun A => S ⊆ A), g A =
      ∑ A' ∈ (pool \ S).powerset, g (S ∪ A') := by
  symm
  apply Finset.sum_nbij' (fun A' => S ∪ A') (fun A => A \ S)
  · intro A' hA'
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset,
      Finset.mem_coe, Finset.mem_powerset] at hA' ⊢
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.union_subset hS (hA'.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
    exact Finset.sdiff_subset_sdiff hA.1 le_rfl
  · intro A' hA'
    simp only [Finset.mem_coe, Finset.mem_powerset] at hA'
    have hd : Disjoint S A' := by
      rw [Finset.disjoint_left]
      intro x hxS hxA
      exact (Finset.mem_sdiff.mp (hA' hxA)).2 hxS
    simp [Finset.union_sdiff_left, hd.symm, Finset.sdiff_eq_self_of_disjoint hd.symm]
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA
    simp [Finset.union_sdiff_of_subset hA.2]
  · intro A' _
    rfl

/-- The `d`-term of `primeMark` is `[img d ⊆ A] · ∏ a_i(d_i)`. -/
theorem tuple_term_eq (slots : Finset σ) (a : σ → ι → ℂ) (d : ∀ i ∈ slots, ι) (A : Finset ι) :
    (∏ i ∈ slots.attach, if d i.1 i.2 ∈ A then a i.1 (d i.1 i.2) else 0) =
      if tupleImg slots d ⊆ A then ∏ i ∈ slots.attach, a i.1 (d i.1 i.2) else 0 := by
  rw [Finset.prod_ite_zero]
  congr 1
  apply propext
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := mem_tupleImg.mp hx
    exact h ⟨i, hi⟩ (Finset.mem_attach _ _)
  · intro h i _
    exact h (mem_tupleImg.mpr ⟨i.1, i.2, rfl⟩)

/-- A tuple from pairwise disjoint lists is injective. -/
theorem tuple_injOn (slots : Finset σ) (lists : σ → Finset ι)
    (hdis : (slots : Set σ).PairwiseDisjoint lists) (d : ∀ i ∈ slots, ι)
    (hd : ∀ i (hi : i ∈ slots), d i hi ∈ lists i) :
    Set.InjOn (fun i : slots => d i.1 i.2) (slots.attach : Set slots) := by
  intro i _ j _ hij
  by_contra hne
  have hne' : i.1 ≠ j.1 := fun h => hne (Subtype.ext h)
  have := hdis i.2 j.2 hne'
  exact Finset.disjoint_left.mp this (hd i.1 i.2) (by simp only at hij; rw [hij]; exact hd j.1 j.2)

/-- **Tuple expansion** of the marked column. -/
theorem markedCol_tuple (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (pool : Finset ι)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (hdis : (slots : Set σ).PairwiseDisjoint lists) (X : ℝ) :
    markedCol c n Φ pool slots lists a X =
      ∑ d ∈ slots.pi lists, if tupleImg slots d ⊆ pool then
        (∏ i ∈ slots.attach, a i.1 (d i.1 i.2) * c (d i.1 i.2)) *
          col c n Φ (pool \ tupleImg slots d) (X / ∏ i ∈ slots.attach, n (d i.1 i.2))
        else 0 := by
  unfold markedCol
  simp_rw [primeMark_eq_tuple_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdl : ∀ i (hi : i ∈ slots), d i hi ∈ lists i := fun i hi => Finset.mem_pi.mp hd i hi
  have hinj := tuple_injOn slots lists hdis d hdl
  simp_rw [tuple_term_eq]
  split_ifs with hsub
  · -- reorganize into the filtered sum
    have h1 : ∀ A ∈ pool.powerset,
        (∏ i ∈ A, c i) * (if tupleImg slots d ⊆ A then ∏ i ∈ slots.attach, a i.1 (d i.1 i.2)
          else 0) * Φ ((∏ i ∈ A, n i) / X) =
        if tupleImg slots d ⊆ A then (∏ i ∈ A, c i) * (∏ i ∈ slots.attach, a i.1 (d i.1 i.2)) *
          Φ ((∏ i ∈ A, n i) / X) else 0 := by
      intro A _; split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter,
      sum_powerset_superset pool (tupleImg slots d) hsub]
    unfold col
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A' hA'
    have hdisj : Disjoint (tupleImg slots d) A' := by
      rw [Finset.disjoint_left]
      intro x hx hxA
      exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hA' hxA)).2 hx
    rw [Finset.prod_union hdisj, Finset.prod_union hdisj]
    have hc : ∏ i ∈ tupleImg slots d, c i = ∏ i ∈ slots.attach, c (d i.1 i.2) :=
      Finset.prod_image hinj
    have hn : ∏ i ∈ tupleImg slots d, n i = ∏ i ∈ slots.attach, n (d i.1 i.2) :=
      Finset.prod_image hinj
    rw [hc, hn, Finset.prod_mul_distrib]
    have hΦ : (∏ i ∈ slots.attach, n (d i.1 i.2)) * (∏ i ∈ A', n i) / X =
        (∏ i ∈ A', n i) / (X / ∏ i ∈ slots.attach, n (d i.1 i.2)) := by
      rw [div_div_eq_mul_div]; ring
    rw [hΦ]; ring
  · apply Finset.sum_eq_zero
    intro A hA
    have : ¬ tupleImg slots d ⊆ A := fun h => hsub (h.trans (Finset.mem_powerset.mp hA))
    simp [this]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.markedCol_tuple
