/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Mathlib

/-!
# Inverse.Poisson.Projector — the complete residual projector

Insert the complete residual projector `∑_{t|a,b} μ(t)` and set `a = t a'`, `b = t b'`. For
squarefree columns inside a pool `R` the disjointness of the two columns is removed exactly:

`∑_{a,b ⊆ R, a ∩ b = ∅} F a G b = ∑_{t ⊆ R} (-1)^|t| (∑_{a' ⊆ R \ t} F (t ∪ a')) (∑_{b' ⊆ R \ t} G (t ∪ b'))`.

No assertion `t | y` is used; the residual columns `a', b'` live on the punctured pool `R \ t`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Supersets of `t` inside `R` are `t ∪ a'` with `a' ⊆ R \ t`. -/
theorem sum_supersets (R t : Finset α) (ht : t ⊆ R) (F : Finset α → ℂ) :
    ∑ a ∈ R.powerset.filter (fun a => t ⊆ a), F a = ∑ a ∈ (R \ t).powerset, F (t ∪ a) := by
  refine Finset.sum_bij' (fun a _ => a \ t) (fun a _ => t ∪ a) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_powerset] at ha
    rw [Finset.mem_powerset]
    exact Finset.sdiff_subset_sdiff ha.1 le_rfl
  · intro a ha
    rw [Finset.mem_powerset] at ha
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.union_subset ht (ha.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.union_sdiff_of_subset ha.2
  · intro a ha
    rw [Finset.mem_powerset] at ha
    exact Finset.union_sdiff_cancel_left
      (Finset.disjoint_of_subset_right ha Finset.disjoint_sdiff)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.union_sdiff_of_subset ha.2]

/-- Möbius inversion of disjointness. -/
theorem disjoint_indicator (R a b : Finset α) (ha : a ⊆ R) :
    (if Disjoint a b then (1 : ℂ) else 0) =
      ∑ t ∈ R.powerset, if t ⊆ a ∧ t ⊆ b then (-1 : ℂ) ^ t.card else 0 := by
  rw [← Finset.sum_filter]
  have hf : R.powerset.filter (fun t => t ⊆ a ∧ t ⊆ b) = (a ∩ b).powerset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans ha, h⟩
  rw [hf]
  have hz := Finset.sum_powerset_neg_one_pow_card (x := a ∩ b)
  have hc : (∑ t ∈ (a ∩ b).powerset, (-1 : ℂ) ^ t.card) =
      ((∑ t ∈ (a ∩ b).powerset, (-1 : ℤ) ^ t.card : ℤ) : ℂ) := by push_cast; rfl
  rw [hc, hz]
  by_cases h : a ∩ b = ∅ <;> simp [Finset.disjoint_iff_inter_eq_empty, h]

/-- The complete residual projector. -/
theorem disjoint_pair_projector (R : Finset α) (F G : Finset α → ℂ) :
    (∑ a ∈ R.powerset, ∑ b ∈ R.powerset, if Disjoint a b then F a * G b else 0) =
      ∑ t ∈ R.powerset, (-1 : ℂ) ^ t.card *
        ((∑ a ∈ (R \ t).powerset, F (t ∪ a)) * ∑ b ∈ (R \ t).powerset, G (t ∪ b)) := by
  calc (∑ a ∈ R.powerset, ∑ b ∈ R.powerset, if Disjoint a b then F a * G b else 0)
      = ∑ a ∈ R.powerset, ∑ b ∈ R.powerset, ∑ t ∈ R.powerset,
          if t ⊆ a ∧ t ⊆ b then (-1 : ℂ) ^ t.card * (F a * G b) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b _
        have h := disjoint_indicator R a b (Finset.mem_powerset.mp ha)
        calc (if Disjoint a b then F a * G b else 0)
            = (if Disjoint a b then (1 : ℂ) else 0) * (F a * G b) := by split_ifs <;> simp
          _ = _ := by
            rw [h, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro t _
            split_ifs <;> simp
    _ = ∑ a ∈ R.powerset, ∑ t ∈ R.powerset, ∑ b ∈ R.powerset,
          if t ⊆ a ∧ t ⊆ b then (-1 : ℂ) ^ t.card * (F a * G b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
    _ = ∑ t ∈ R.powerset, ∑ a ∈ R.powerset, ∑ b ∈ R.powerset,
          if t ⊆ a ∧ t ⊆ b then (-1 : ℂ) ^ t.card * (F a * G b) else 0 :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        have htR := Finset.mem_powerset.mp ht
        rw [← sum_supersets R t htR F, ← sum_supersets R t htR G, Finset.sum_mul_sum,
          Finset.mul_sum]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases hta : t ⊆ a
        · rw [ite_eq_left hta, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          by_cases htb : t ⊆ b <;> simp [hta, htb]
        · rw [ite_eq_right hta]
          apply Finset.sum_eq_zero
          intro b _
          simp [hta]

end Qrh.MarkedAnchor.Inverse.Poisson
