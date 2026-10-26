/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Weighted frozen/live splitting, using the unchanged assignment equivalence
from PR69. The residual may depend on its live assignment; it is never
replaced by the sum of absolute values of individual live coefficients.
-/
import Candidate.FourthPower.KernelHoleCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelAssignmentReindex
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.Record12518109GainDeletion

variable {I A R : Type*} [Fintype I] [Fintype A] [CommSemiring R]

def weightedSum (a : I → A → R) (f : (I → A) → R) : R :=
  ∑ x : I → A, if Function.Injective x then f x * ∏ i, a i (x i) else 0

def remainingSum (T : Finset I) (a : I → A → R) (t : T → A)
    (f : ({i // i ∉ T} → A) → R) : R :=
  ∑ s : {i // i ∉ T} → A,
    if Function.Injective s ∧ (∀ i j, t i ≠ s j) then
      f s * ∏ j : {i // i ∉ T}, a j.val (s j) else 0

/-- Both within-part injectivity and all cross-distinctness holes are retained. -/
theorem split_weighted (T : Finset I) (a : I → A → R)
    (f : (T → A) → ({i // i ∉ T} → A) → R) :
    weightedSum a (fun x => f (fun i => x i.val) (fun j => x j.val)) =
      ∑ t : T → A, if Function.Injective t then
        (∏ i : T, a i.val (t i)) * remainingSum T a t (f t) else 0 := by
  unfold weightedSum
  rw [← (assignmentSplit (A := A) (fun i => i ∈ T)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro t _
  by_cases ht : Function.Injective t
  · rw [if_pos ht]
    unfold remainingSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr (by ext; simp)
    intro s _
    change (if Function.Injective (joinAssignments (fun i => i ∈ T) t s) then
      f (fun i => joinAssignments (fun i => i ∈ T) t s i.val)
        (fun j => joinAssignments (fun i => i ∈ T) t s j.val) *
        ∏ i, a i (joinAssignments (fun i => i ∈ T) t s i) else 0) = _
    have hf : (fun i : T => joinAssignments (fun i => i ∈ T) t s i.val) = t := by
      funext i; simp [joinAssignments,i.property]
    have hl : (fun j : {i // i ∉ T} => joinAssignments (fun i => i ∈ T) t s j.val) = s := by
      funext j; simp [joinAssignments,j.property]
    rw [hf,hl]
    simp only [injective_joinAssignments,joinAssignments_product]
    by_cases h : Function.Injective s ∧ (∀ i j, t i ≠ s j)
    · simp only [ht,h.1,true_and]
      rw [if_pos h.2,if_pos h.2]
      ring_nf
      congr 2 <;> first
      | rfl
      | (apply Finset.prod_congr (by ext; simp); intros; rfl)
      | (apply Finset.ext; intro i; simp)
    · simp only [ht,h,true_and,ite_false,mul_zero]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro s _
    change (if Function.Injective (joinAssignments (fun i => i ∈ T) t s) then _ else 0) = 0
    simp [injective_joinAssignments,ht]

theorem weightedSum_sum {B : Type*} (D : Finset B) (a : I → A → R)
    (f : B → (I → A) → R) :
    weightedSum a (fun x => ∑ d ∈ D, f d x) = ∑ d ∈ D, weightedSum a (f d) := by
  unfold weightedSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Function.Injective x <;> simp [hx,Finset.sum_mul]

theorem remainingSum_sum {B : Type*} (D : Finset B) (T : Finset I)
    (a : I → A → R) (t : T → A) (f : B → ({i // i ∉ T} → A) → R) :
    remainingSum T a t (fun s => ∑ d ∈ D, f d s) =
      ∑ d ∈ D, remainingSum T a t (f d) := by
  unfold remainingSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Function.Injective s ∧ (∀ i j, t i ≠ s j) <;>
    simp [hs,Finset.sum_mul]

theorem remainingSum_mul (T : Finset I) (a : I → A → R) (t : T → A)
    (k : R) (f : ({i // i ∉ T} → A) → R) :
    remainingSum T a t (fun s => k * f s) = k * remainingSum T a t f := by
  unfold remainingSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Function.Injective s ∧ (∀ i j, t i ≠ s j) <;> simp [hs,mul_assoc]

/-- Kernels depending on frozen labels stay outside the whole residual row. -/
theorem split_convolution {B : Type*} (D : Finset B) (T : Finset I)
    (a : I → A → R) (k : (T → A) → B → R)
    (f : B → ({i // i ∉ T} → A) → R) :
    weightedSum a (fun x => ∑ d ∈ D,
      k (fun i => x i.val) d * f d (fun j => x j.val)) =
      ∑ t : T → A, if Function.Injective t then ∑ d ∈ D,
        (k t d * ∏ i : T, a i.val (t i)) * remainingSum T a t (f d) else 0 := by
  rw [split_weighted T a (fun t s => ∑ d ∈ D, k t d * f d s)]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t
  · simp only [ht,ite_true,remainingSum_sum,remainingSum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · simp [ht]

theorem remainingSum_constant (T : Finset I) (a : I → A → R) (t : T → A) (c : R) :
    remainingSum T a t (fun _ => c) = c * injectiveTuplePolynomial
      (fun j : {i // i ∉ T} => fun p => if ∀ i : T, t i ≠ p then a j.val p else 0) := by
  unfold remainingSum injectiveTuplePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro s _
  by_cases hs : Function.Injective s
  · rw [if_pos hs,Fintype.prod_ite_zero]
    by_cases hc : ∀ i : T, ∀ j : {i // i ∉ T}, t i ≠ s j
    · have hc' : ∀ j : {i // i ∉ T}, ∀ i : T, t i ≠ s j := fun j i => hc i j
      simp only [hs,true_and]
      rw [if_pos hc,if_pos hc']
    · have hc' : ¬ (∀ j : {i // i ∉ T}, ∀ i : T, t i ≠ s j) := fun h => hc (fun i j => h j i)
      simp only [hs,hc,hc',true_and,ite_false,mul_zero]
  · simp [hs]

end
end Candidate.FourthPower.KernelAssignmentReindex
