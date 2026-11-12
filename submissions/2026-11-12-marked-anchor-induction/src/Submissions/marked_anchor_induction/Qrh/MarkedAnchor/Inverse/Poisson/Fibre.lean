/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.InnerSum
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Counting

/-!
# Inverse.Poisson.Fibre — the physical row of a label and the label multiplicity

* `physRow_eq`, `physRow_mem_span`: `y = f² (∏_g p) g' k`, so every prime of `g` divides `y`
  (this supplies the `g`-zero of the child rows).
* `physRow_norm_sq`: `‖y‖² = (N f)² · N g · ‖g'‖² · ‖k‖²` and `N e · ‖g'‖² = N g`.
* `fibre_card_le`: for `y ≠ 0` the labels `(f, g, E, k)` with row `y` inject into
  `(divisors of y)³` (divisor-many labels per row; the dual frequency is then determined).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open OAI.FirstPassCubeLabels (primeProductNorm)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem physRow_eq (f : O) (g E : Finset ι) (hE : E ⊆ g) (k : O) :
    physRow p f g E k = f ^ 2 * (∏ i ∈ g, p i) * cofactor p g E * k := by
  unfold physRow
  rw [← cofactor_spec p g E hE]

theorem physRow_mem_span (f : O) (g E : Finset ι) (hE : E ⊆ g) (k : O) (i : ι) (hi : i ∈ g) :
    physRow p f g E k ∈ Ideal.span {p i} := by
  rw [physRow_eq p f g E hE, Ideal.mem_span_singleton]
  have : p i ∣ ∏ j ∈ g, p j := Finset.dvd_prod_of_mem p hi
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left this _) _) _

theorem neg_physRow_mem_span (f : O) (g E : Finset ι) (hE : E ⊆ g) (k : O) (i : ι) (hi : i ∈ g) :
    -physRow p f g E k ∈ Ideal.span {p i} :=
  (Ideal.span {p i}).neg_mem (physRow_mem_span p f g E hE k i hi)

theorem eis_norm_sq_mul (x y : O) :
    ‖eisEmbedding (x * y)‖ ^ 2 = ‖eisEmbedding x‖ ^ 2 * ‖eisEmbedding y‖ ^ 2 := by
  rw [map_mul, norm_mul, mul_pow]

theorem physRow_norm_sq (f : O) (g E : Finset ι) (hE : E ⊆ g) (k : O) :
    ‖eisEmbedding (physRow p f g E k)‖ ^ 2 =
      (‖eisEmbedding f‖ ^ 2) ^ 2 * primeProductNorm p g * ‖eisEmbedding (cofactor p g E)‖ ^ 2 *
        ‖eisEmbedding k‖ ^ 2 := by
  rw [physRow_eq p f g E hE, eis_norm_sq_mul, eis_norm_sq_mul, eis_norm_sq_mul, pow_two f,
    eis_norm_sq_mul, FirstPassCubeLabels.primeProductNorm]
  ring

theorem gen_cofactor_norm (g E : Finset ι) (hE : E ⊆ g) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
      ‖eisEmbedding (cofactor p g E)‖ ^ 2 = primeProductNorm p g := by
  rw [← eis_norm_sq_mul, ← cofactor_spec p g E hE, FirstPassCubeLabels.primeProductNorm]

/-- The label → row map. -/
def labelRow (l : Ideal O × Finset ι × Finset ι × O) : O :=
  physRow p (CompletedGauss.primaryGenerator l.1) l.2.1 l.2.2.1 l.2.2.2

include hinj in
theorem fibre_card_le (S : Finset (Ideal O × Finset ι × Finset ι × O))
    (hS : ∀ l ∈ S, CompletedGauss.primaryGenerator l.1 ≠ 0 ∧ l.2.2.1 ⊆ l.2.1)
    (y : O) (hy : y ≠ 0) :
    ((S.filter (fun l => labelRow p l = y)).card : ℝ) ≤
      ((idealDivisors (Ideal.span {y})).card : ℝ) ^ 3 := by
  set D := idealDivisors (Ideal.span {y})
  have hyb : Ideal.span {y} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hy
  let F : Ideal O × Finset ι × Finset ι × O → Ideal O × Ideal O × Ideal O :=
    fun l => (l.1, colIdeal p l.2.1, colIdeal p l.2.2.1)
  have hmaps : ∀ l ∈ S.filter (fun l => labelRow p l = y), F l ∈ D ×ˢ D ×ˢ D := by
    intro l hl
    obtain ⟨hlS, hly⟩ := Finset.mem_filter.mp hl
    obtain ⟨hφ, hEg⟩ := hS l hlS
    have hydef : y = CompletedGauss.primaryGenerator l.1 ^ 2 * (∏ i ∈ l.2.1, p i) *
        cofactor p l.2.1 l.2.2.1 * l.2.2.2 := by
      rw [← hly]; unfold labelRow; exact physRow_eq p _ _ _ hEg _
    have hGy : (∏ i ∈ l.2.1, p i) ∣ y := by
      rw [hydef]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_mul_left _ _) _) _
    have hdiv : ∀ x : O, x ∣ y → Ideal.span {x} ∣ Ideal.span {y} := fun x hx =>
      Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hx)
    simp only [Finset.mem_product, F]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_idealDivisors hyb, ← (CompletedGauss.primaryGenerator_spec l.1 hφ).1]
      apply hdiv
      rw [hydef]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self _
        (by norm_num)) _) _) _
    · rw [mem_idealDivisors hyb, colIdeal_eq_span]
      exact hdiv _ hGy
    · rw [mem_idealDivisors hyb, colIdeal_eq_span]
      exact hdiv _ ((Finset.prod_dvd_prod_of_subset _ _ p hEg).trans hGy)
  have hinjOn : Set.InjOn F (S.filter (fun l => labelRow p l = y)) := by
    intro l₁ hl₁ l₂ hl₂ hF
    obtain ⟨hl₁S, hy₁⟩ := Finset.mem_filter.mp hl₁
    obtain ⟨hl₂S, hy₂⟩ := Finset.mem_filter.mp hl₂
    simp only [F, Prod.mk.injEq] at hF
    obtain ⟨h1, h2, h3⟩ := hF
    have hg : l₁.2.1 = l₂.2.1 := prodSpan_injective p hinj h2
    have hE : l₁.2.2.1 = l₂.2.2.1 := prodSpan_injective p hinj h3
    have hk : l₁.2.2.2 = l₂.2.2.2 := by
      unfold labelRow physRow at hy₁ hy₂
      rw [h1, hg, hE] at hy₁
      rw [← hy₂] at hy₁
      have hc : CompletedGauss.primaryGenerator l₂.1 ^ 2 *
          (primeSubsetGenerator (fun i => Ideal.span {p i}) l₂.2.2.1 *
            cofactor p l₂.2.1 l₂.2.2.1) * cofactor p l₂.2.1 l₂.2.2.1 ≠ 0 := by
        intro h0
        apply hy
        rw [← hy₂, h0, zero_mul]
      exact mul_left_cancel₀ hc hy₁
    rcases l₁ with ⟨a1, b1, c1, d1⟩
    rcases l₂ with ⟨a2, b2, c2, d2⟩
    simp only at h1 hg hE hk
    rw [h1, hg, hE, hk]
  calc ((S.filter (fun l => labelRow p l = y)).card : ℝ)
      = (((S.filter (fun l => labelRow p l = y)).image F).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinjOn]
    _ ≤ ((D ×ˢ D ×ˢ D).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (fun x hx => by
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
          exact hmaps l hl)
    _ = (D.card : ℝ) ^ 3 := by
        rw [Finset.card_product, Finset.card_product]; push_cast; ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
