/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Whole-slot forced/filled/exhausted dispatch on the unchanged original support.
Uses the established Sil whole-slot greedy source through small_select_on. -/
import Candidate.C092.transport.OrderedPairClosureInduction
import Candidate.C092.transport.StrongPairSmallSelect

set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairClosure
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle092.StrongPair

/-- Selection precedes rows and keeps every forced original slot. Exhaustion
retains the entire actual live set, including zero-width slots. Otherwise
forced width already meets the target, or a genuine whole-slot filling lies
within one mesh of it. No pointwise amplitude lower is imposed. -/
theorem original_support_dispatch {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (live forced : Finset Slot) (hforced : forced⊆live) (w : Slot→ℝ) (mesh target : ℝ)
    (hw : ∀ i,0≤w i) (hwm : ∀ i,w i≤ mesh) (hm : 0≤ mesh) (ht : 0≤target) :
    ∃ selected : Finset Slot, forced⊆selected ∧ selected⊆live ∧
      ((∑ i∈live,w i)≤target → selected=live) ∧
      (((∑ i∈live,w i)≤target ∧ selected=live) ∨
        (target≤(∑ i∈forced,w i) ∧ selected=forced) ∨
        ((∑ i∈selected,w i)≤target ∧ target-mesh≤(∑ i∈selected,w i))) := by
  by_cases hall : (∑ i∈live,w i)≤target
  · exact ⟨live,hforced,le_rfl,fun _=>rfl,Or.inl ⟨hall,rfl⟩⟩
  by_cases hforce : target≤(∑ i∈forced,w i)
  · exact ⟨forced,le_rfl,hforced,fun h=>False.elim (hall h),Or.inr (Or.inl ⟨hforce,rfl⟩)⟩
  have hremain : 0≤target-(∑ i∈forced,w i) := sub_nonneg.mpr (le_of_not_ge hforce)
  obtain ⟨R,hR,hcap,hrest⟩ := small_select_on (live\forced) w mesh
    (target-(∑ i∈forced,w i)) hw hwm hm hremain
  let selected := forced∪R
  have hsel : selected⊆live := Finset.union_subset hforced (hR.trans Finset.sdiff_subset)
  have hdisj : Disjoint forced R := Finset.disjoint_left.mpr (by
    intro i hi hir
    exact (Finset.mem_sdiff.mp (hR hir)).2 hi)
  have hsum : (∑ i∈selected,w i)=(∑ i∈forced,w i)+(∑ i∈R,w i) := Finset.sum_union hdisj
  have hsrem : (∑ i∈live\forced,w i)=(∑ i∈live,w i)-(∑ i∈forced,w i) :=
    Finset.sum_sdiff_eq_sub hforced
  have hset : live\selected=(live\forced)\R := by ext i; simp [selected]; tauto
  have hrest' : (∑ i∈live\selected,w i) ≤ (∑ i∈live,w i)-target+mesh := by
    rw [hset]
    apply hrest.trans_eq
    rw [hsrem]
    have hnonneg : 0≤(∑ i∈live,w i)-(∑ i∈forced,w i)-
        (target-(∑ i∈forced,w i))+mesh := by linarith [lt_of_not_ge hall]
    rw [max_eq_right hnonneg]
    ring
  rw [Finset.sum_sdiff_eq_sub hsel] at hrest'
  refine ⟨selected,Finset.subset_union_left,hsel,fun h=>False.elim (hall h),Or.inr (Or.inr ⟨?_,?_⟩)⟩
  · linarith [hsum]
  · linarith

#print axioms original_support_dispatch
end
end QRH.Cycle092.OrderedPairClosure
