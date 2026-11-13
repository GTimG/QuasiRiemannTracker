/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Inverse.Select.Choice

Whole-slot selection: whole live slots of total width just below the target. For slots of width `≤ mesh` and a target `u` not exceeding the
total live width there is a subcollection `R` with `u - mesh ≤ ∑_R w ≤ u`. If the live width is
below the target, the `u = 0` branch applies (`live_selection_or_low`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse

open scoped BigOperators

/-- Greedy form: a subcollection with sum `≤ u` that is either within `mesh` of `u` or all. -/
theorem greedy_selection {σ : Type} [DecidableEq σ] (w : σ → ℝ) (mesh : ℝ)
    (J : Finset σ) (hw : ∀ i ∈ J, 0 ≤ w i) (hmesh : ∀ i ∈ J, w i ≤ mesh) (u : ℝ) (hu : 0 ≤ u) :
    ∃ R ⊆ J, (∑ i ∈ R, w i) ≤ u ∧ (u - mesh ≤ ∑ i ∈ R, w i ∨ R = J) := by
  induction J using Finset.induction_on with
  | empty => exact ⟨∅, le_rfl, by simpa using hu, Or.inr rfl⟩
  | insert a J ha ih =>
    have hw' : ∀ i ∈ J, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hm' : ∀ i ∈ J, w i ≤ mesh := fun i hi => hmesh i (Finset.mem_insert_of_mem hi)
    obtain ⟨R, hRJ, hRu, hR⟩ := ih hw' hm'
    rcases hR with hR | rfl
    · exact ⟨R, hRJ.trans (Finset.subset_insert a J), hRu, Or.inl hR⟩
    · by_cases hfit : (∑ i ∈ R, w i) + w a ≤ u
      · refine ⟨insert a R, le_rfl, ?_, Or.inr rfl⟩
        rw [Finset.sum_insert ha]; linarith
      · have hfit' := lt_of_not_ge hfit
        have hwa := hmesh a (Finset.mem_insert_self a R)
        exact ⟨R, Finset.subset_insert a R, hRu, Or.inl (by linarith)⟩

/-- Whole slots of total width in `[u - mesh, u]`. -/
theorem live_selection {σ : Type} [DecidableEq σ] (w : σ → ℝ) (mesh : ℝ) (hmesh0 : 0 ≤ mesh)
    (J : Finset σ) (hw : ∀ i ∈ J, 0 ≤ w i) (hmesh : ∀ i ∈ J, w i ≤ mesh) (u : ℝ) (hu : 0 ≤ u)
    (hlive : u ≤ ∑ i ∈ J, w i) :
    ∃ R ⊆ J, u - mesh ≤ (∑ i ∈ R, w i) ∧ (∑ i ∈ R, w i) ≤ u := by
  obtain ⟨R, hRJ, hRu, hR⟩ := greedy_selection w mesh J hw hmesh u hu
  rcases hR with hR | rfl
  · exact ⟨R, hRJ, hR, hRu⟩
  · exact ⟨R, le_rfl, by linarith, hRu⟩

/-- Either a selection of width in `[u - mesh, u]` exists, or the live width is below `u`
(the `u = 0` branch). -/
theorem live_selection_or_low {σ : Type} [DecidableEq σ] (w : σ → ℝ) (mesh : ℝ)
    (hmesh0 : 0 ≤ mesh) (J : Finset σ) (hw : ∀ i ∈ J, 0 ≤ w i) (hmesh : ∀ i ∈ J, w i ≤ mesh) (u : ℝ) (hu : 0 ≤ u) :
    (∃ R ⊆ J, u - mesh ≤ (∑ i ∈ R, w i) ∧ (∑ i ∈ R, w i) ≤ u) ∨ (∑ i ∈ J, w i) < u := by
  rcases le_or_gt u (∑ i ∈ J, w i) with h | h
  · exact Or.inl (live_selection w mesh hmesh0 J hw hmesh u hu h)
  · exact Or.inr h

/-- The residual (unselected) live width after a selection `R ⊆ J`. -/
theorem residual_width {σ : Type} [DecidableEq σ] (w : σ → ℝ) (J R : Finset σ) (hR : R ⊆ J) :
    (∑ i ∈ J \ R, w i) = (∑ i ∈ J, w i) - (∑ i ∈ R, w i) := by
  rw [Finset.sum_sdiff_eq_sub hR]

end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.live_selection
