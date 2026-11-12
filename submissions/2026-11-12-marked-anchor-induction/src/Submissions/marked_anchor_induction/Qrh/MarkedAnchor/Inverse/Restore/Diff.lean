/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Split

/-!
# Inverse.Restore.Diff — main term minus physical term = frozen terms

For tuple primes `U ⊆ S` (the column pool), the main exact-image column `mCol` (full column) and
the physical one `gCol` (required primes avoided by the column) differ by the doubled primes:

`mCol U S I X - gCol U S I X = ∑_{F ⊆ I, F ≠ ∅} ∑_{B ⊆ U, |B| = |F|} mark_F(B) · (∏_B c²) ·
  gCol (U \ B) (S \ B) (I \ F) (X / ∏_B n²)` (`mCol_sub_gCol`).

The slots of `F` are FROZEN on the primes of `B` (weight `c²`, i.e. `N p^{-1}`, the `j ≥ 2`
powers of the reciprocal Euler factor, `Restore/Euler`); the remaining slots `I \ F` form a physical column of the same kind with fewer
slots, which is the input of the strong induction in `Restore/Bound`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators

variable {σ ι : Type*} [DecidableEq ι]

/-- The column on `S` is the avoided column plus the nonempty required parts of `T`. -/
theorem col_eq_sdiff_add (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S T : Finset ι) (hT : T ⊆ S)
    (hn : ∀ i, n i ≠ 0) (Y : ℝ) :
    col c n Φ S Y = col c n Φ (S \ T) Y +
      ∑ B ∈ T.powerset \ {∅}, (∏ i ∈ B, c i) * col c n Φ (S \ T) (Y / ∏ i ∈ B, n i) := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset hT]
  rw [col_union c n Φ (S \ T) T Finset.sdiff_disjoint (fun q _ => hn q),
    ← Finset.sum_sdiff (s₁ := ({∅} : Finset (Finset ι)))
      (Finset.singleton_subset_iff.mpr (Finset.empty_mem_powerset T)), Finset.sum_singleton]
  simp only [Finset.prod_empty, one_mul, div_one]
  rw [add_comm]
  try congr 1

/-- **Main minus physical = frozen terms.** -/
theorem mCol_sub_gCol (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (hUS : U ⊆ S)
    (hn : ∀ i, n i ≠ 0) (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    mCol c n Φ U S I L a X - gCol c n Φ U S I L a X =
      ∑ F ∈ I.powerset \ {∅}, ∑ B ∈ U.powerset.filter (fun B => B.card = F.card),
        primeMarkInj F L a B * ((∏ i ∈ B, c i ^ 2) *
          gCol c n Φ (U \ B) (S \ B) (I \ F) L a (X / ∏ i ∈ B, n i ^ 2)) := by
  unfold mCol gCol
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ T ∈ U.powerset.filter (fun T => T.card = I.card),
      primeMarkInj I L a T * ((∏ i ∈ T, c i) * col c n Φ S (X / ∏ i ∈ T, n i)) -
        primeMarkInj I L a T * ((∏ i ∈ T, c i) * col c n Φ (S \ T) (X / ∏ i ∈ T, n i)) =
      ∑ B ∈ T.powerset \ {∅}, ∑ F ∈ I.powerset.filter (fun F => F.card = B.card),
        primeMarkInj F L a B * primeMarkInj (I \ F) L a (T \ B) * ((∏ i ∈ T, c i) *
          ((∏ i ∈ B, c i) * col c n Φ (S \ T) ((X / ∏ i ∈ T, n i) / ∏ i ∈ B, n i))) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    rw [col_eq_sdiff_add c n Φ S T (hT.1.trans hUS) hn, ← mul_sub, ← mul_sub,
      add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    have hBT : B ⊆ T := Finset.mem_powerset.mp (Finset.mem_sdiff.mp hB).1
    rw [primeMarkInj_split I L a T B hBT hT.2, Finset.sum_mul]
  rw [Finset.sum_congr rfl h1]
  -- swap `T` and `B`
  have hsw1 : ∀ T B, T ∈ U.powerset.filter (fun T => T.card = I.card) ∧ B ∈ T.powerset \ {∅} ↔
      T ∈ (U.powerset.filter (fun T => T.card = I.card)).filter (fun T => B ⊆ T) ∧
        B ∈ U.powerset \ {∅} := by
    intro T B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h3.trans h1, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [Finset.sum_comm' hsw1]
  rw [Finset.sum_congr rfl (fun B _ => Finset.sum_comm)]
  -- swap `B` and `F`
  have hsw2 : ∀ B F, B ∈ U.powerset \ {∅} ∧ F ∈ I.powerset.filter (fun F => F.card = B.card) ↔
      B ∈ U.powerset.filter (fun B => B.card = F.card) ∧ F ∈ I.powerset \ {∅} := by
    intro B F
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨h1, h4.symm⟩, h3, ?_⟩
      rintro rfl
      exact h2 (Finset.card_eq_zero.mp (by simpa using h4.symm))
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨h1, ?_⟩, h3, h2.symm⟩
      rintro rfl
      exact h4 (Finset.card_eq_zero.mp (by simpa using h2.symm))
  rw [Finset.sum_comm' hsw2]
  apply Finset.sum_congr rfl
  intro F hF
  apply Finset.sum_congr rfl
  intro B hB
  simp only [Finset.mem_sdiff, Finset.mem_powerset, Finset.mem_singleton] at hF
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  have hIF : (I \ F).card + F.card = I.card := Finset.card_sdiff_add_card_eq_card hF.1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_nbij' (fun T => T \ B) (fun T' => B ∪ T')
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    have h := Finset.card_sdiff_add_card_eq_card hT.2
    refine ⟨Finset.sdiff_subset_sdiff hT.1.1 le_rfl, ?_⟩
    omega
  · intro T' hT'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT' ⊢
    have hd : Disjoint B T' := by
      rw [Finset.disjoint_left]
      intro x hxB hxT
      exact (Finset.mem_sdiff.mp (hT'.1 hxT)).2 hxB
    refine ⟨⟨Finset.union_subset hB.1 (hT'.1.trans Finset.sdiff_subset), ?_⟩,
      Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint hd]
    omega
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.union_sdiff_of_subset hT.2
  · intro T' hT'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT'
    have hd : Disjoint T' B := by
      rw [Finset.disjoint_left]
      intro x hxT hxB
      exact (Finset.mem_sdiff.mp (hT'.1 hxT)).2 hxB
    rw [Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hd
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have hBT := hT.2
    have hS : S \ T = (S \ B) \ (T \ B) := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun h => h2 (hBT h)⟩, fun h => h2 h.1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun h => h3 ⟨h, h2⟩⟩
    have hcT : ∏ i ∈ T, c i = (∏ i ∈ T \ B, c i) * ∏ i ∈ B, c i := (Finset.prod_sdiff hBT).symm
    have hnT : ∏ i ∈ T, n i = (∏ i ∈ T \ B, n i) * ∏ i ∈ B, n i := (Finset.prod_sdiff hBT).symm
    have hc2 : ∏ i ∈ B, c i ^ 2 = (∏ i ∈ B, c i) ^ 2 := Finset.prod_pow B 2 c
    have hn2 : ∏ i ∈ B, n i ^ 2 = (∏ i ∈ B, n i) ^ 2 := Finset.prod_pow B 2 n
    rw [hcT, hnT, hS, hc2, hn2]
    have hsc : X / ((∏ i ∈ T \ B, n i) * ∏ i ∈ B, n i) / ∏ i ∈ B, n i =
        X / (∏ i ∈ B, n i) ^ 2 / ∏ i ∈ T \ B, n i := by
      rw [div_div, div_div]
      congr 1
      ring
    rw [hsc]
    ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mCol_sub_gCol
