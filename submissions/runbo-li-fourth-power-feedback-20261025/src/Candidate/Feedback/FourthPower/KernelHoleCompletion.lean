/- Copyright (c) 2026 Sil. Apache-2.0.
Exact full-pool-minus-forbidden completion for injective labelled prime slots.
Every nontrivial correction has fewer live labels. The frozen coefficients
are supported on the actual forbidden sets, not on the full prime pool.
-/
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.DeletionCollisionAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.KernelHoleCompletion
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.Record12518109GainDeletion

variable {I A : Type*} [Fintype I] [Fintype A]

def good (a : I → A → ℂ) (forbidden : I → A → Prop) (i : I) (p : A) : ℂ :=
  if forbidden i p then 0 else a i p

def bad (a : I → A → ℂ) (forbidden : I → A → Prop) (i : I) (p : A) : ℂ :=
  if forbidden i p then a i p else 0

def mixed (a : I → A → ℂ) (forbidden : I → A → Prop) (L : Finset I) (i : I) (p : A) : ℂ :=
  if i ∈ L then good a forbidden i p else bad a forbidden i p

omit [Fintype I] [Fintype A] in
theorem good_add_bad (a : I → A → ℂ) (forbidden : I → A → Prop) (i : I) (p : A) :
    good a forbidden i p + bad a forbidden i p = a i p := by
  by_cases h : forbidden i p <;> simp [good,bad,h]

omit [Fintype A] in
theorem product_partition (a : I → A → ℂ) (forbidden : I → A → Prop) (x : I → A) :
    (∏ i, a i (x i)) = ∑ L : Finset I, ∏ i, mixed a forbidden L i (x i) := by
  have h := Fintype.prod_add (fun i => good a forbidden i (x i))
    (fun i => bad a forbidden i (x i))
  simp_rw [good_add_bad] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro L _
  have hc : (Finset.univ.filter (fun i => i ∉ L)) = Lᶜ := by ext i; simp
  simp only [mixed,Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter,hc]

theorem full_partition (a : I → A → ℂ) (forbidden : I → A → Prop) :
    injectiveTuplePolynomial a =
      ∑ L : Finset I, injectiveTuplePolynomial (mixed a forbidden L) := by
  unfold injectiveTuplePolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : Function.Injective x
  · simp only [h,ite_true]
    exact product_partition a forbidden x
  · simp [h]

omit [Fintype A] in
theorem mixed_all (a : I → A → ℂ) (forbidden : I → A → Prop) :
    mixed a forbidden Finset.univ = good a forbidden := by
  funext i p
  simp [mixed]

/-- Every correction on the right has a proper subset of live labels. -/
theorem complete_holes (a : I → A → ℂ) (forbidden : I → A → Prop) :
    injectiveTuplePolynomial (good a forbidden) = injectiveTuplePolynomial a -
      ∑ L ∈ (Finset.univ : Finset (Finset I)).erase Finset.univ,
        injectiveTuplePolynomial (mixed a forbidden L) := by
  apply eq_sub_iff_add_eq.mpr
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset I))
    (fun L => injectiveTuplePolynomial (mixed a forbidden L)) (Finset.mem_univ Finset.univ)
  rw [← full_partition a forbidden,mixed_all] at h
  simpa only [add_comm] using h

/-- Frozen assignments retain their coefficients and all cross-distinctness
conditions. No arbitrary subset estimate is used to justify this equality. -/
theorem freeze_forbidden (a : I → A → ℂ) (forbidden : I → A → Prop) (L : Finset I) :
    injectiveTuplePolynomial (mixed a forbidden L) =
      ∑ t : {i // i ∉ L} → A, if Function.Injective t then
        (∏ j : {i // i ∉ L}, bad a forbidden j.val (t j))*
          injectiveTuplePolynomial (fun i : {i // i ∈ L} => fun p =>
            if ∀ j : {i // i ∉ L}, p ≠ t j then good a forbidden i.val p else 0)
      else 0 := by
  have hl (i : {i // i ∈ L}) (p : A) : mixed a forbidden L i.val p = good a forbidden i.val p := by
    simp [mixed,i.property]
  have hf (i : {i // i ∉ L}) (p : A) : mixed a forbidden L i.val p = bad a forbidden i.val p := by
    simp [mixed,i.property]
  have h := injectiveTuplePolynomial_split (fun i => i ∈ L) (mixed a forbidden L)
  simp only [hl,hf] at h
  convert h using 1
  apply Finset.sum_congr (by ext; simp)
  intro t _
  split_ifs
  · apply congrArg₂ (·*·)
    · apply Finset.prod_congr (by ext; simp)
      intro j _
      rfl
    · unfold injectiveTuplePolynomial
      apply Finset.sum_congr (by ext; simp)
      intro x _
      split_ifs
      · apply Finset.prod_congr (by ext; simp)
        intro i _
        rfl
      · rfl
  · rfl

omit [Fintype A] in
theorem frozen_support (a : I → A → ℂ) (forbidden : I → A → Prop) (L : Finset I)
    (t : {i // i ∉ L} → A)
    (h : (∏ j : {i // i ∉ L}, bad a forbidden j.val (t j)) ≠ 0) :
    ∀ j : {i // i ∉ L}, forbidden j.val (t j) := by
  intro j
  have hj := (Finset.prod_ne_zero_iff.mp h) j (Finset.mem_univ j)
  by_contra hn
  exact hj (by simp [bad,hn])

theorem fewer_live_labels (L : Finset I) (hL : L ≠ Finset.univ) :
    Fintype.card {i // i ∈ L} < Fintype.card I := by
  rw [Fintype.card_coe]
  simpa using Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ L,hL⟩)

end
end Candidate.Feedback.FourthPower.KernelHoleCompletion
