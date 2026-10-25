/- Copyright (c) 2026 Sil. Apache-2.0.
Positive reduction of the whole original supplier family BEFORE K4.
The selected character zeros and D-dependent residual polynomial survive.
-/
import Candidate.Feedback.FourthPower.MixedSupplierOriginalFrequency

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedSupplierOuterFamily
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstColumns
open MixedSupplierKernel MixedSupplierFourthRow MixedSupplierPositive
open MixedSupplierOuterActive MixedSupplierOriginalFrequency
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem original_family_active (q : Data α) (x : Frozen q)
    (τ : Character) (t : ℝ) (k : O) :
    originalFamily q x τ t k = ∑y∈activeSelected q,selectedRow q x y τ t k := by
  unfold originalFamily activeSelected
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hi : Function.Injective y
  · by_cases hw : selectedWeight q y=0
    · simp only [hi,hw,ne_eq,not_true_eq_false,and_false,ite_false,ite_true,
        selected_row_zero q x y hw τ t k]
    · simp only [hi,hw,ne_eq,not_false_eq_true,and_self,ite_true]
  · simp only [hi,false_and,ite_false]

/-- The scalar majorant is independent of k but retains the actual
original character's natural zeros, essential for fresh-D forcing. -/
theorem selected_row_sq (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (y : Selected q) (hy : Function.Injective y) (seed : Id)
    (hseed : q.u=frozenProduct q x*seed) (τ : Character) (t : ℝ) (k : O) :
    ‖selectedRow q x y τ t k‖^2 ≤
      256*∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
        (selectedPositiveWeight q x y τ*‖originalPolynomial q x y seed τ t ξ k‖^2) := by
  rw [selected_row_original q x y seed hseed τ t k]
  simp only [mul_assoc]
  apply (first_ray_sq (fun χ ξ=>selectedScalar q x y τ t k χ*
    originalPolynomial q x y seed τ t ξ k)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ξ hξ
  exact mul_le_mul_of_nonneg_left
    (original_ray_sq_le_positive q x hx y hy seed τ t χ ξ k) (norm_nonneg _)

theorem original_family_sq (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (seed : Id) (hseed : q.u=frozenProduct q x*seed)
    (τ : Character) (t : ℝ) (k : O) :
    ‖originalFamily q x τ t k‖^2 ≤
      256*((activeSelected q).card:ℝ)*
        ∑y∈activeSelected q,∑χ : RayCharacter,∑ξ : RayCharacter,
          ‖pairCoeff firstPhaseTable χ ξ‖*
            (selectedPositiveWeight q x y τ*‖originalPolynomial q x y seed τ t ξ k‖^2) := by
  rw [original_family_active]
  apply (CubicEisenstein.norm_sum_sq_le_card (activeSelected q)
    (fun y=>selectedRow q x y τ t k)).trans
  calc
    _ ≤ ((activeSelected q).card:ℝ)*∑y∈activeSelected q,
        256*∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
          (selectedPositiveWeight q x y τ*‖originalPolynomial q x y seed τ t ξ k‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro y hy
      exact selected_row_sq q x hx y (Finset.mem_filter.mp hy).2.1 seed hseed τ t k
    _ = _ := by rw [←Finset.mul_sum];ring

/-- One residual seed is chosen before every character, height, frequency
pool and nonnegative radial weight. This is the actual outer family, with
the frozen square and the single selected-cardinality Cauchy cost. -/
theorem uniform_weighted_original_sum (q : Data α) (x : Frozen q)
    (hx : Function.Injective x) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ : Character)(t : ℝ)(Ks : Finset O)(ρ : O→ℝ),(∀k∈Ks,0≤ρ k)→
      (∑k∈Ks,ρ k*‖frozenWeight q x*originalFamily q x τ t k‖^2) ≤
        ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
          ∑y∈activeSelected q,∑χ : RayCharacter,∑ξ : RayCharacter,
            ‖pairCoeff firstPhaseTable χ ξ‖*selectedPositiveWeight q x y τ*
              ∑k∈Ks,ρ k*‖originalPolynomial q x y seed τ t ξ k‖^2) := by
  by_cases hw : frozenWeight q x=0
  · refine ⟨1,by simp only [hw,ne_eq,not_true_eq_false,false_implies],?_⟩
    intro τ t Ks ρ hρ
    simp only [hw,zero_mul,norm_zero,zero_pow (by decide : 2≠0),mul_zero,
      Finset.sum_const_zero,le_refl]
  · obtain ⟨seed,hs⟩ := frozen_divides q x hx hw
    refine ⟨seed,fun _=>hs,?_⟩
    intro τ t Ks ρ hρ
    have hpoint (k : O) (hk : k∈Ks) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (original_family_sq q x hx seed hs τ t k)
          (sq_nonneg ‖frozenWeight q x‖)) (hρ k hk)
    simp only [norm_mul,mul_pow]
    apply (Finset.sum_le_sum hpoint).trans_eq
    simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ξ hξ
    apply Finset.sum_congr rfl
    intro k hk
    ring

end
end Candidate.Feedback.FourthPower.MixedSupplierOuterFamily
