/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.InnerSum

/-!
# Inverse.Poisson.Tail — the rapid tail outside the physical row ball

For dual frequencies `k` outside a finite set `K` (containing every `k` whose physical row is in
the ball), every live pair `(a, b)` has kernel argument `≥ T`, so by
`paperRadialFourier_lattice_tail` the tail is `O((1+T)^(-A))` times the trivial pair mass.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem tsum_compl_le_superset (f : O → ℝ) (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f)
    (s : Set O) (t : Set O) (hst : s ⊆ t) :
    ∑' k : s, f k ≤ ∑' k : t, f k := by
  have hinj : Function.Injective (fun k : s => (⟨k.1, hst k.2⟩ : t)) := by
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  exact tsum_comp_le_tsum_of_inj (f := fun k : t => f k) (hf.subtype t) (fun k => hf0 k) hinj

include hp in
theorem innerPair_norm_le (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (g E : Finset ι) (k : O) (a b : Finset ι) :
    ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ ≤
      bigGBound p hp hcop hg Ψ m f H g a b / ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ *
        ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖ := by
  unfold innerPair
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hB := bigG_norm_le p hp hcop hg Ψ m f H g a b E k
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / kernelDen p E a b =
      Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2 := by ring
  rw [harg]
  have hn := norm_nonneg (paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2))
  have hd := norm_nonneg (eisEmbedding (∏ i ∈ activeSupport a b, p i))
  calc ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖ /
        ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ * ‖bigG p hp hcop hg Ψ m f H g a b E k‖
      ≤ ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖ /
        ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ * bigGBound p hp hcop hg Ψ m f H g a b :=
        mul_le_mul_of_nonneg_left hB (div_nonneg hn hd)
    _ = _ := by ring

theorem bigGBound_nonneg (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a b : Finset ι) :
    0 ≤ bigGBound p hp hcop hg Ψ m f H g a b := by
  unfold bigGBound; positivity

include hp in
/-- The rapid tail of the residual pair sum over the dual frequencies in `s`. -/
theorem inner_tail_le (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (g E : Finset ι) (s : Set O) (T : ℝ)
    (hs : ∀ a ∈ (pool \ g).powerset, ∀ b ∈ (pool \ g).powerset, Disjoint a b →
      bigGBound p hp hcop hg Ψ m f H g a b ≠ 0 →
      ∀ k ∈ s, T ≤ Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)
    (Ctail : ℝ → ℝ)
    (htail : ∀ K : ℝ, 0 < K →
      (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤ Ctail K) :
    ∑' k : s, ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖ ≤
      ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
        if Disjoint a b then
          bigGBound p hp hcop hg Ψ m f H g a b / ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ *
            Ctail (Y / kernelDen p E a b) else 0 := by
  have hK : ∀ a b : Finset ι, 0 < Y / kernelDen p E a b :=
    fun a b => div_pos hY (kernelDen_pos p hp E a b)
  have hsumW : ∀ a b : Finset ι, Summable (fun k : O =>
      ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖) :=
    fun a b => EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ (hK a b)
  have hpairS : ∀ a b : Finset ι, Summable (fun k : s =>
      ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖) :=
    fun a b => ((innerPair_summable p hp hcop hg Ψ m f H W Y hY g E a b).norm).subtype s
  have hbound : ∀ k : O, ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖ ≤
      ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
        ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ := by
    intro k
    unfold inner
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    split_ifs <;> simp
  have hbound' : ∀ k : O, ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖ ≤
      ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
        (if Disjoint a b then ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ else 0) := by
    intro k
    unfold inner
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    split_ifs <;> simp
  have hRS : Summable (fun k : s => ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
      ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖) :=
    summable_sum fun a _ => summable_sum fun b _ => hpairS a b
  have hLS : Summable (fun k : s => ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖) :=
    hRS.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k)
  have hpairS' : ∀ a b : Finset ι, Summable (fun k : s =>
      if Disjoint a b then ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ else 0) := by
    intro a b; by_cases hd : Disjoint a b
    · simp only [hd, if_true]; exact hpairS a b
    · simp only [hd, if_false]; exact summable_zero
  have hRS' : Summable (fun k : s => ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
      (if Disjoint a b then ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ else 0)) :=
    summable_sum fun a _ => summable_sum fun b _ => hpairS' a b
  calc ∑' k : s, ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖
      ≤ ∑' k : s, ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
          (if Disjoint a b then ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ else 0) :=
        hLS.tsum_le_tsum (fun k => hbound' k) hRS'
    _ = ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
          ∑' k : s, (if Disjoint a b then ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖ else 0) := by
        rw [Summable.tsum_finsetSum (fun a _ => summable_sum fun b _ => hpairS' a b)]
        apply Finset.sum_congr rfl; intro a _
        rw [Summable.tsum_finsetSum (fun b _ => hpairS' a b)]
    _ ≤ _ := by
        apply Finset.sum_le_sum; intro a ha
        apply Finset.sum_le_sum; intro b hb
        by_cases hd : Disjoint a b
        swap
        · simp [hd]
        simp only [hd, if_true]
        have hc0 : 0 ≤ bigGBound p hp hcop hg Ψ m f H g a b /
            ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ :=
          div_nonneg (bigGBound_nonneg p hp hcop hg Ψ m f H g a b) (norm_nonneg _)
        calc ∑' k : s, ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖
            ≤ ∑' k : s, bigGBound p hp hcop hg Ψ m f H g a b /
                ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ *
                ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding (k : O)‖ ^ 2)‖ :=
              (hpairS a b).tsum_le_tsum (fun k => innerPair_norm_le p hp hcop hg Ψ m f H W Y g E k a b)
                (((hsumW a b).subtype s).mul_left _)
          _ = bigGBound p hp hcop hg Ψ m f H g a b /
                ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ *
              ∑' k : s, ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding (k : O)‖ ^ 2)‖ :=
              tsum_mul_left
          _ ≤ _ := by
              by_cases h0 : bigGBound p hp hcop hg Ψ m f H g a b = 0
              · rw [h0]; simp
              · apply mul_le_mul_of_nonneg_left _ hc0
                refine (tsum_compl_le_superset _ (fun k => norm_nonneg _) (hsumW a b) s
                  {h : O | T ≤ Y / kernelDen p E a b * ‖eisEmbedding h‖ ^ 2}
                  (fun k hk => hs a ha b hb hd h0 k hk)).trans ?_
                exact htail _ (hK a b)

end
end Qrh.MarkedAnchor.Inverse.Poisson
