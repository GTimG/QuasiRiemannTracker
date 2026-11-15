/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.RowSplit

/-!
# Inverse.Select.Cauchy — central Cauchy and the row injection `k ↦ k D⁴`

After the selection identity (`canonical_row_select`) the row at `k` is
`∑_D c_D · X_D(e_D k)` with `e_D k = k D⁴`. With a common profile (after the profile separation,
`Select/Separate`) the
central Cauchy–Schwarz inequality and the multiplicity of the map `(D, k) ↦ e_D k` give

  `∑_{k} |∑_D c_D X(e_D k)|² ≤ (∑_D |c_D|²) · mult · ∑_{k' ∈ K'} |X k'|²`

where `K' ⊇ e_D(K)` (the enlarged row ball `Z^(K+4u+η)`) and `mult` bounds the fibres
(`#{(D,k) : k D⁴ = k'} ≤ τ`). `cauchy_rows_family` is the version with a finite family of
separated profiles `X_j` and bounded weights `g_j(D)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse

open scoped BigOperators

/-- Cauchy–Schwarz for a finite complex sum. -/
theorem norm_sum_mul_sq_le {α : Type*} (s : Finset α) (c x : α → ℂ) :
    ‖∑ D ∈ s, c D * x D‖^2 ≤ (∑ D ∈ s, ‖c D‖^2) * ∑ D ∈ s, ‖x D‖^2 := by
  have h1 : ‖∑ D ∈ s, c D * x D‖ ≤ ∑ D ∈ s, ‖c D‖ * ‖x D‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have hcs : (∑ D ∈ s, ‖c D‖ * ‖x D‖)^2 ≤ (∑ D ∈ s, ‖c D‖^2) * ∑ D ∈ s, ‖x D‖^2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun D => ‖c D‖) (fun D => ‖x D‖)
  have h0 : 0 ≤ ‖∑ D ∈ s, c D * x D‖ := norm_nonneg _
  calc ‖∑ D ∈ s, c D * x D‖^2 ≤ (∑ D ∈ s, ‖c D‖ * ‖x D‖)^2 := by gcongr
    _ ≤ _ := hcs

/-- The central Cauchy step with the row injection: the multiplicity of `(D,k) ↦ e D k`. -/
theorem cauchy_rows {α β : Type*} [DecidableEq β] (Ds : Finset α) (ks ks' : Finset β)
    (c : α → ℂ) (X : β → ℂ) (e : α → β → β)
    (hmap : ∀ D ∈ Ds, ∀ k ∈ ks, e D k ∈ ks') (mult : ℕ)
    (hmult : ∀ k' ∈ ks', ((Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k')).card ≤ mult) :
    ∑ k ∈ ks, ‖∑ D ∈ Ds, c D * X (e D k)‖^2 ≤
      (∑ D ∈ Ds, ‖c D‖^2) * mult * ∑ k' ∈ ks', ‖X k'‖^2 := by
  have hC0 : 0 ≤ ∑ D ∈ Ds, ‖c D‖^2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have step1 : ∑ k ∈ ks, ‖∑ D ∈ Ds, c D * X (e D k)‖^2 ≤
      ∑ k ∈ ks, (∑ D ∈ Ds, ‖c D‖^2) * ∑ D ∈ Ds, ‖X (e D k)‖^2 :=
    Finset.sum_le_sum (fun k _ => norm_sum_mul_sq_le Ds c (fun D => X (e D k)))
  have step2 : ∑ k ∈ ks, ∑ D ∈ Ds, ‖X (e D k)‖^2 =
      ∑ x ∈ Ds ×ˢ ks, ‖X (e x.1 x.2)‖^2 := by
    rw [Finset.sum_product_right]
  have step3 : ∑ x ∈ Ds ×ˢ ks, ‖X (e x.1 x.2)‖^2 =
      ∑ k' ∈ ks', ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), ‖X (e x.1 x.2)‖^2 := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro x hx
    exact hmap x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
  have step4 : ∑ k' ∈ ks', ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'),
      ‖X (e x.1 x.2)‖^2 ≤ ∑ k' ∈ ks', (mult : ℝ) * ‖X k'‖^2 := by
    apply Finset.sum_le_sum
    intro k' hk'
    have hconst : ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), ‖X (e x.1 x.2)‖^2 =
        ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), ‖X k'‖^2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast hmult k' hk'
  calc ∑ k ∈ ks, ‖∑ D ∈ Ds, c D * X (e D k)‖^2
      ≤ ∑ k ∈ ks, (∑ D ∈ Ds, ‖c D‖^2) * ∑ D ∈ Ds, ‖X (e D k)‖^2 := step1
    _ = (∑ D ∈ Ds, ‖c D‖^2) * ∑ x ∈ Ds ×ˢ ks, ‖X (e x.1 x.2)‖^2 := by
        rw [← Finset.mul_sum, step2]
    _ ≤ (∑ D ∈ Ds, ‖c D‖^2) * ∑ k' ∈ ks', (mult : ℝ) * ‖X k'‖^2 := by
        rw [step3]; exact mul_le_mul_of_nonneg_left step4 hC0
    _ = (∑ D ∈ Ds, ‖c D‖^2) * mult * ∑ k' ∈ ks', ‖X k'‖^2 := by
        rw [← Finset.mul_sum]; ring

/-- Separated profiles: `X_D = ∑_j g j D · X_j` with a finite family; Cauchy over `j` costs `J`. -/
theorem cauchy_rows_family {α β : Type*} [DecidableEq β] (Ds : Finset α) (ks ks' : Finset β)
    (c : α → ℂ) {J : ℕ} (g : Fin J → α → ℂ) (Xs : Fin J → β → ℂ) (e : α → β → β)
    (hmap : ∀ D ∈ Ds, ∀ k ∈ ks, e D k ∈ ks') (mult : ℕ)
    (hmult : ∀ k' ∈ ks', ((Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k')).card ≤ mult)
    (G : ℝ) (hg : ∀ j, ∀ D ∈ Ds, ‖g j D‖ ≤ G) :
    ∑ k ∈ ks, ‖∑ D ∈ Ds, c D * ∑ j, g j D * Xs j (e D k)‖^2 ≤
      J * (G^2 * ((∑ D ∈ Ds, ‖c D‖^2) * mult)) * ∑ j, ∑ k' ∈ ks', ‖Xs j k'‖^2 := by
  have hswap : ∀ k, (∑ D ∈ Ds, c D * ∑ j, g j D * Xs j (e D k)) =
      ∑ j : Fin J, ∑ D ∈ Ds, (c D * g j D) * Xs j (e D k) := by
    intro k
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro D _
    ring
  have hjcs : ∀ k, ‖∑ j : Fin J, ∑ D ∈ Ds, (c D * g j D) * Xs j (e D k)‖^2 ≤
      J * ∑ j : Fin J, ‖∑ D ∈ Ds, (c D * g j D) * Xs j (e D k)‖^2 := by
    intro k
    have h := norm_sum_mul_sq_le (Finset.univ : Finset (Fin J)) (fun _ => (1:ℂ))
      (fun j => ∑ D ∈ Ds, (c D * g j D) * Xs j (e D k))
    simpa using h
  have hcg : ∀ j, (∑ D ∈ Ds, ‖c D * g j D‖^2) ≤ G^2 * ∑ D ∈ Ds, ‖c D‖^2 := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    rw [norm_mul, mul_pow, mul_comm]
    have := hg j D hD
    gcongr
  calc ∑ k ∈ ks, ‖∑ D ∈ Ds, c D * ∑ j, g j D * Xs j (e D k)‖^2
      = ∑ k ∈ ks, ‖∑ j : Fin J, ∑ D ∈ Ds, (c D * g j D) * Xs j (e D k)‖^2 := by
        simp only [hswap]
    _ ≤ ∑ k ∈ ks, J * ∑ j : Fin J, ‖∑ D ∈ Ds, (c D * g j D) * Xs j (e D k)‖^2 :=
        Finset.sum_le_sum (fun k _ => hjcs k)
    _ = J * ∑ j : Fin J, ∑ k ∈ ks, ‖∑ D ∈ Ds, (c D * g j D) * Xs j (e D k)‖^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ J * ∑ j : Fin J, (∑ D ∈ Ds, ‖c D * g j D‖^2) * mult * ∑ k' ∈ ks', ‖Xs j k'‖^2 := by
        gcongr with j
        exact cauchy_rows Ds ks ks' (fun D => c D * g j D) (Xs j) e hmap mult hmult
    _ ≤ J * ∑ j : Fin J, (G^2 * ∑ D ∈ Ds, ‖c D‖^2) * mult * ∑ k' ∈ ks', ‖Xs j k'‖^2 := by
        gcongr with j
        exact hcg j
    _ = J * (G^2 * ((∑ D ∈ Ds, ‖c D‖^2) * mult)) * ∑ j, ∑ k' ∈ ks', ‖Xs j k'‖^2 := by
        have hj : ∀ j : Fin J, (G^2 * ∑ D ∈ Ds, ‖c D‖^2) * mult * ∑ k' ∈ ks', ‖Xs j k'‖^2 =
            (G^2 * ((∑ D ∈ Ds, ‖c D‖^2) * mult)) * ∑ k' ∈ ks', ‖Xs j k'‖^2 := fun j => by ring
        simp only [hj, ← Finset.mul_sum]
        ring

end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.cauchy_rows
#print axioms Qrh.MarkedAnchor.Inverse.cauchy_rows_family
