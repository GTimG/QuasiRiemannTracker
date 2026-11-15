/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.LabelInt

/-!
# Inverse.Poisson.CellBound — paying one cell by the child hypothesis

* `blocked_fibre`: `∑_l w_l F(i_l, z_l) ≤ wmax · fib · ∑_{i ≤ I} ∑_{y ∈ ball} F(i, y)`.
* `isChildRay_conj`, `isChildRay_plain`: the cell twists are child rays.
* `cell_child_sum_le`: `∑_{y ∈ ball} ‖child‖² ≤ B (1+|s|)^(2d)` from `ChildBoundInj` (also for
  punctures `N t > Gmax`, where the child row vanishes identically).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter)

local notation "O" => ActualEisensteinCubic.O

/-- Blocked fibre bound. -/
theorem blocked_fibre {L : Type*} (S : Finset L) (iof : L → ℕ) (zof : L → O) (w : L → ℝ)
    (F : ℕ → O → ℝ) (ball : Finset O) (I : ℕ) (wmax fib : ℝ) (hwmax : 0 ≤ wmax)
    (hw0 : ∀ l ∈ S, 0 ≤ w l) (hw : ∀ l ∈ S, w l ≤ wmax) (hF : ∀ i y, 0 ≤ F i y)
    (hI : ∀ l ∈ S, iof l ≤ I) (hz : ∀ l ∈ S, zof l ∈ ball)
    (hfib : ∀ y ∈ ball, ((S.filter (fun l => zof l = y)).card : ℝ) ≤ fib) :
    ∑ l ∈ S, w l * F (iof l) (zof l) ≤
      wmax * fib * ∑ i ∈ Finset.range (I + 1), ∑ y ∈ ball, F i y := by
  have h1 : ∑ l ∈ S, w l * F (iof l) (zof l) ≤ wmax * ∑ l ∈ S, F (iof l) (zof l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_right (hw l hl) (hF _ _)
  have hmap : ∀ l ∈ S, iof l ∈ Finset.range (I + 1) :=
    fun l hl => Finset.mem_range.mpr (Nat.lt_succ_of_le (hI l hl))
  have h2 : ∑ l ∈ S, F (iof l) (zof l) ≤
      ∑ i ∈ Finset.range (I + 1), fib * ∑ y ∈ ball, F i y := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_le_sum
    intro i _
    have hcongr : ∑ l ∈ S.filter (fun l => iof l = i), F (iof l) (zof l) =
        ∑ l ∈ S.filter (fun l => iof l = i), (1 : ℝ) * F i (zof l) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [(Finset.mem_filter.mp hl).2, one_mul]
    rw [hcongr]
    apply fibre_sum_le _ zof (fun _ => (1 : ℝ)) (F i) ball fib (fun _ _ => zero_le_one)
      (fun y => hF i y) (fun l hl => hz l (Finset.mem_filter.mp hl).1)
    intro y hy
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    refine le_trans ?_ (hfib y hy)
    exact_mod_cast Finset.card_le_card (fun l hl => by
      simp only [Finset.mem_filter] at hl ⊢
      exact ⟨hl.1.1, hl.2⟩)
  calc ∑ l ∈ S, w l * F (iof l) (zof l)
      ≤ wmax * ∑ l ∈ S, F (iof l) (zof l) := h1
    _ ≤ wmax * ∑ i ∈ Finset.range (I + 1), fib * ∑ y ∈ ball, F i y :=
        mul_le_mul_of_nonneg_left h2 hwmax
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem rayMonoid_conj_mul (θ χ : RayCharacter) (Ψ : O →* ℂ) :
    rayMonoid θ * (conjugateRayMonoid χ * Ψ) = rayMonoid (θ * χ⁻¹) * Ψ := by
  ext u
  simp only [MonoidHom.mul_apply, SecondPassArithmetic.rayMonoid_apply,
    SecondPassArithmetic.conjugateRayMonoid_apply, RayFourExpansion.rayCharacter,
    MulChar.coeToFun_mul, Pi.mul_apply, MulChar.star_apply']
  ring

theorem rayMonoid_mul_mul (θ η : RayCharacter) (Ψ : O →* ℂ) :
    rayMonoid θ * (rayMonoid η * Ψ) = rayMonoid (θ * η) * Ψ := by
  ext u
  simp only [MonoidHom.mul_apply, SecondPassArithmetic.rayMonoid_apply,
    RayFourExpansion.rayCharacter, MulChar.coeToFun_mul, Pi.mul_apply]
  ring

theorem isChildRay_conj (θ χ : RayCharacter) (Ψ : O →* ℂ) :
    IsChildRay Ψ (rayMonoid θ * (conjugateRayMonoid χ * Ψ)) :=
  ⟨θ * χ⁻¹, rayMonoid_conj_mul θ χ Ψ⟩

theorem isChildRay_plain (θ η : RayCharacter) (Ψ : O →* ℂ) :
    IsChildRay Ψ (rayMonoid θ * (rayMonoid η * Ψ)) :=
  ⟨θ * η, rayMonoid_mul_mul θ η Ψ⟩

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- A child row whose profile vanishes beyond `2 bo` is zero for large punctures. -/
theorem childRow_zero_large (pool t : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (bo X : ℝ) (i : ℕ) (s : ℝ) (z : O)
    (hX : 0 < X) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (ht : 2 * bo * X < primeProductNorm p t) :
    mobiusChildRowInj p hg (pool \ t) ψ m slots lists a (childLogTest Φ s)
      (X / (2 ^ i * primeProductNorm p t)) true z = 0 := by
  unfold mobiusChildRowInj
  apply Finset.sum_eq_zero
  intro A _
  have hNt := FirstPassCubeLabels.primeProductNorm_pos p hp t
  have hNA : 1 ≤ primeProductNorm p A := one_le_primeProductNorm p hp A
  have hpow : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hx : 2 * bo < primeProductNorm p A / (X / (2 ^ i * primeProductNorm p t)) := by
    rw [div_div_eq_mul_div, lt_div_iff₀ hX]
    calc 2 * bo * X < primeProductNorm p t := ht
      _ ≤ primeProductNorm p A * (2 ^ i * primeProductNorm p t) := by
        have h1 : 1 ≤ primeProductNorm p A * 2 ^ i := one_le_mul_of_one_le_of_one_le hNA hpow
        calc primeProductNorm p t = 1 * primeProductNorm p t := (one_mul _).symm
          _ ≤ (primeProductNorm p A * 2 ^ i) * primeProductNorm p t :=
            mul_le_mul_of_nonneg_right h1 hNt.le
          _ = _ := by ring
  rw [childLogTest, hΦ _ hx]
  simp

end
end Qrh.MarkedAnchor.Inverse.Poisson
