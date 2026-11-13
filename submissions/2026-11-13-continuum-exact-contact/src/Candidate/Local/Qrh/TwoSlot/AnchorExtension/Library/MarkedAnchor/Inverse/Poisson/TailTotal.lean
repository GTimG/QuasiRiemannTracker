/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Norms
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.PairSep

/-!
# Inverse.Poisson.TailTotal — the rapid tail of one label, summed over `g, E`

`∑_g ∑_E (Y/N e) ∑'_{out} ‖inner‖ ≤ Cl · gSum² · Y · 128² (bo X)³ ∑_U ‖H U‖²`, with
`Cl = Ct · sem(Ŵ) · (1 + (bo X)⁴) / (1+T₀)^A`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem entryH_norm (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ)
    (s₀ X : ℝ) (U : Finset ι) :
    ‖entryH p slots lists a W s₀ X U‖ =
      ‖primeMarkInj slots lists a U‖ * ‖W (primeProductNorm p U / X)‖ := by
  unfold entryH; rw [norm_mul, childLogTest_norm]

theorem entryH_live (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ)
    (s₀ X bo : ℝ) (hX : 0 < X) (hW : ∀ x, W x ≠ 0 → x ≤ bo) (U : Finset ι)
    (hU : entryH p slots lists a W s₀ X U ≠ 0) : primeProductNorm p U ≤ bo * X := by
  have hW0 : W (primeProductNorm p U / X) ≠ 0 := by
    intro h0; apply hU; unfold entryH childLogTest; rw [h0]; simp
  have := hW _ hW0
  rwa [div_le_iff₀ hX] at this

include hp in
theorem gen_norm_sq_le (g E : Finset ι) (hE : E ⊆ g) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 ≤ primeProductNorm p g := by
  rw [gen_norm_sq, ← Finset.union_sdiff_of_subset hE,
    FirstPassCubeLabels.primeProductNorm_union p E (g \ E) Finset.disjoint_sdiff]
  have := one_le_primeProductNorm p hp (g \ E)
  have := FirstPassCubeLabels.primeProductNorm_pos p hp E
  nlinarith

include hp in
theorem one_le_gen_norm_sq (E : Finset ι) :
    1 ≤ ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 := by
  rw [gen_norm_sq]; exact one_le_primeProductNorm p hp E

include hp in
theorem sumE_le (g : Finset ι) (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ E ∈ g.powerset.attach,
      Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 ≤
        Y * primeProductNorm p g := by
  calc ∑ E ∈ g.powerset.attach,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2
      ≤ ∑ _E ∈ g.powerset.attach, Y := by
        apply Finset.sum_le_sum; intro E _
        exact div_le_self hY (one_le_gen_norm_sq p hp E.1)
    _ = Y * (2 : ℝ) ^ g.card := by
        rw [Finset.sum_const, Finset.card_attach, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring
    _ ≤ Y * primeProductNorm p g :=
        mul_le_mul_of_nonneg_left (two_pow_card_le_primeProductNorm p hp g) hY

theorem sum_sub_le (pool g : Finset ι) (h : Finset ι → ℝ) (h0 : ∀ U, 0 ≤ h U) :
    ∑ a ∈ (pool \ g).powerset, h (g ∪ a) ≤ ∑ U ∈ (pool ∪ g).powerset, h U := by
  have hinj : Set.InjOn (fun a => g ∪ a) ((pool \ g).powerset : Set (Finset ι)) := by
    intro a ha b hb hab
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_powerset] at ha hb
    have hda : Disjoint g a := Finset.disjoint_of_subset_right ha Finset.disjoint_sdiff
    have hdb : Disjoint g b := Finset.disjoint_of_subset_right hb Finset.disjoint_sdiff
    simp only at hab
    rw [← Finset.union_sdiff_cancel_left hda, hab, Finset.union_sdiff_cancel_left hdb]
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro U hU
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.mem_powerset] at ha ⊢
    exact Finset.union_subset Finset.subset_union_right (ha.trans
      (Finset.sdiff_subset.trans Finset.subset_union_left))
  · intro U _ _; exact h0 U

include hp in
theorem minK_inv_le (Y X bo : ℝ) (hY : 1 ≤ Y) (hboX : 0 ≤ bo * X) (g E a b : Finset ι)
    (hE : E ⊆ g) (hab : Disjoint a b)
    (ha : primeProductNorm p g * primeProductNorm p a ≤ bo * X)
    (hb : primeProductNorm p g * primeProductNorm p b ≤ bo * X) :
    ((min 1 (Y / kernelDen p E a b)) ^ 2)⁻¹ ≤ 1 + (bo * X) ^ 4 := by
  have hden : kernelDen p E a b ≤ (bo * X) ^ 2 := by
    unfold kernelDen
    rw [norm_eis_active p hp a b hab, mul_pow, Real.sq_sqrt (FirstPassCubeLabels.primeProductNorm_pos p hp a).le,
      Real.sq_sqrt (FirstPassCubeLabels.primeProductNorm_pos p hp b).le]
    have he := gen_norm_sq_le p hp g E hE
    have hg1 := one_le_primeProductNorm p hp g
    have hNa := FirstPassCubeLabels.primeProductNorm_pos p hp a
    have hNb := FirstPassCubeLabels.primeProductNorm_pos p hp b
    have he0 : 0 ≤ ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 := by positivity
    calc ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          (primeProductNorm p a * primeProductNorm p b)
        ≤ primeProductNorm p g * (primeProductNorm p a * primeProductNorm p b) := by gcongr
      _ ≤ (primeProductNorm p g * primeProductNorm p a) * (primeProductNorm p g * primeProductNorm p b) := by
          have h0 : 0 ≤ primeProductNorm p g * (primeProductNorm p a * primeProductNorm p b) :=
            mul_nonneg (by linarith) (mul_pos hNa hNb).le
          calc primeProductNorm p g * (primeProductNorm p a * primeProductNorm p b)
              = 1 * (primeProductNorm p g * (primeProductNorm p a * primeProductNorm p b)) := by ring
            _ ≤ primeProductNorm p g * (primeProductNorm p g * (primeProductNorm p a * primeProductNorm p b)) :=
                mul_le_mul_of_nonneg_right hg1 h0
            _ = _ := by ring
      _ ≤ (bo * X) * (bo * X) := mul_le_mul ha hb (by positivity) hboX
      _ = (bo * X) ^ 2 := by ring
  have hpos := kernelDen_pos p hp E a b
  have hK : 1 / (bo * X) ^ 2 ≤ Y / kernelDen p E a b ∨ bo * X = 0 := by
    rcases eq_or_lt_of_le hboX with h0 | h0
    · exact Or.inr h0.symm
    · left
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith
  rcases hK with hK | h0
  · have hm : min 1 (1 / (bo * X) ^ 2) ≤ min 1 (Y / kernelDen p E a b) := min_le_min le_rfl hK
    have hm0 : 0 < min 1 (1 / (bo * X) ^ 2) := by
      apply lt_min one_pos
      have : 0 < (bo * X) ^ 2 := lt_of_lt_of_le hpos hden
      positivity
    calc ((min 1 (Y / kernelDen p E a b)) ^ 2)⁻¹ ≤ ((min 1 (1 / (bo * X) ^ 2)) ^ 2)⁻¹ := by
          apply inv_anti₀ (by positivity); exact pow_le_pow_left₀ hm0.le hm 2
      _ ≤ 1 + (bo * X) ^ 4 := by
          rcases le_total 1 (1 / (bo * X) ^ 2) with h1 | h1
          · rw [min_eq_left h1]; norm_num; positivity
          · rw [min_eq_right h1]
            have : 0 < (bo * X) ^ 2 := lt_of_lt_of_le hpos hden
            rw [div_pow, one_pow, inv_div, div_one, ← pow_mul]
            norm_num
  · exfalso
    rw [h0] at hden
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    linarith [hpos]

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem sq_sum_live_le (pool : Finset ι) (h : Finset ι → ℝ) (L : ℝ)
    (hlive : ∀ U ∈ pool.powerset, h U ≠ 0 →
      U ∈ pool.powerset.filter (fun U => primeProductNorm p U ≤ L))
    (hcard : ((pool.powerset.filter (fun U => primeProductNorm p U ≤ L)).card : ℝ) ≤ 128 * L) :
    (∑ U ∈ pool.powerset, h U) ^ 2 ≤ 128 * L * ∑ U ∈ pool.powerset, h U ^ 2 := by
  set S := pool.powerset.filter (fun U => primeProductNorm p U ≤ L)
  have hsplit : ∑ U ∈ pool.powerset, h U = ∑ U ∈ S, h U := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U hU hUS
    by_contra hne
    exact hUS (hlive U hU hne)
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := h)
  have hsub : ∑ U ∈ S, h U ^ 2 ≤ ∑ U ∈ pool.powerset, h U ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun U _ _ => sq_nonneg _)
  rw [hsplit]
  calc (∑ U ∈ S, h U) ^ 2 ≤ (S.card : ℝ) * ∑ U ∈ S, h U ^ 2 := by exact_mod_cast hcs
    _ ≤ 128 * L * ∑ U ∈ pool.powerset, h U ^ 2 := by
        apply mul_le_mul hcard hsub (Finset.sum_nonneg fun U _ => sq_nonneg _)
        have := (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
        linarith

include hp in
theorem tail_f_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (s₀ X : ℝ) (hX : 0 < X) (bo : ℝ)
    (hboX : 1 ≤ bo * X) (hW : ∀ x, W x ≠ 0 → x ≤ bo) (Wk : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY1 : 1 ≤ Y)
    (f : O) (hf : f ≠ 0) (ball : Finset O) (T0 : ℝ) (hT0 : 0 ≤ T0) (Cw : ℝ) (hCw : 0 ≤ Cw) (At : ℕ)
    (hlat : ∀ K : ℝ, 0 < K →
      (∑' h : {h : O // T0 ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier Wk (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        Cw / ((min 1 K) ^ 2 * (1 + T0) ^ At))
    (hs : ∀ g ∈ pool.powerset, ∀ E (hE : E ∈ g.powerset), ∀ a' ∈ (pool \ g).powerset,
      ∀ b' ∈ (pool \ g).powerset, Disjoint a' b' →
      bigGBound p hp hcop hg Ψ m f (entryH p slots lists a W s₀ X) g a' b' ≠ 0 →
      ∀ k ∈ {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E (Finset.mem_powerset.mp hE) ball},
        T0 ≤ Y / kernelDen p E a' b' * ‖eisEmbedding k‖ ^ 2) :
    ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset.attach,
      Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
        ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) ball},
          ‖inner p hp hcop hg pool Ψ m f (entryH p slots lists a W s₀ X) Wk Y g E.1 k‖ ≤
      (Cw * (1 + (bo * X) ^ 4) / (1 + T0) ^ At) * gSum ^ 2 * Y * (bo * X) *
        (128 * (bo * X)) * (128 * (bo * X) *
          ∑ U ∈ pool.powerset, ‖entryH p slots lists a W s₀ X U‖ ^ 2) := by
  set H := entryH p slots lists a W s₀ X with hH
  have hP : 0 < (1 + T0) ^ At := pow_pos (by linarith) _
  set Cl := Cw * (1 + (bo * X) ^ 4) / (1 + T0) ^ At with hCl
  have hCl0 : 0 ≤ Cl := div_nonneg (mul_nonneg hCw (by positivity)) hP.le
  have hG := gSum_nonneg
  have hY0 : 0 ≤ Y := by linarith
  have hlive : ∀ U, H U ≠ 0 → primeProductNorm p U ≤ bo * X :=
    fun U hU => entryH_live p slots lists a W s₀ X bo hX hW U hU
  -- one (g, E)
  have hgE : ∀ g ∈ pool.powerset, ∀ E (hE : E ∈ g.powerset),
      ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E (Finset.mem_powerset.mp hE) ball},
          ‖inner p hp hcop hg pool Ψ m f H Wk Y g E k‖ ≤
        Cl * gSum ^ 2 * (∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖) ^ 2 := by
    intro g hgp E hE
    refine (inner_tail_le p hp hcop hg pool Ψ m f H Wk Y (by linarith) g E _ T0 (hs g hgp E hE)
      (fun K => Cw / ((min 1 K) ^ 2 * (1 + T0) ^ At)) hlat).trans ?_
    calc _ ≤ ∑ a' ∈ (pool \ g).powerset, ∑ b' ∈ (pool \ g).powerset,
          Cl * gSum ^ 2 * (‖H (g ∪ a')‖ * ‖H (g ∪ b')‖) := by
          apply Finset.sum_le_sum; intro a' ha'
          apply Finset.sum_le_sum; intro b' hb'
          have hnn : 0 ≤ Cl * gSum ^ 2 * (‖H (g ∪ a')‖ * ‖H (g ∪ b')‖) :=
            mul_nonneg (mul_nonneg hCl0 (sq_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          by_cases hd : Disjoint a' b'
          swap
          · simp only [hd, ite_false]; exact hnn
          simp only [hd, ite_true]
          by_cases h0 : bigGBound p hp hcop hg Ψ m f H g a' b' = 0
          · rw [h0]; simp only [zero_div, zero_mul]; exact hnn
          have hbB := bigGBound_le p hp hcop hg hinj hc hpr Ψ hΨ m f H g a' b'
          have hb0 := bigGBound_nonneg p hp hcop hg Ψ m f H g a' b'
          have hHa : H (g ∪ a') ≠ 0 := by
            intro h; apply h0
            exact le_antisymm (by simpa [h] using hbB) hb0
          have hHb : H (g ∪ b') ≠ 0 := by
            intro h; apply h0
            exact le_antisymm (by simpa [h] using hbB) hb0
          have hga : Disjoint g a' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp ha')
            Finset.disjoint_sdiff
          have hgb : Disjoint g b' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hb')
            Finset.disjoint_sdiff
          have hla := hlive _ hHa
          have hlb := hlive _ hHb
          rw [FirstPassCubeLabels.primeProductNorm_union p g a' hga] at hla
          rw [FirstPassCubeLabels.primeProductNorm_union p g b' hgb] at hlb
          have hmin := minK_inv_le p hp Y X bo hY1 (by linarith) g E a' b'
            (Finset.mem_powerset.mp hE) hd hla hlb
          have hn1 : 1 ≤ ‖eisEmbedding (∏ i ∈ activeSupport a' b', p i)‖ := by
            rw [norm_eis_active p hp a' b' hd]
            have h1 := one_le_primeProductNorm p hp a'
            have h2 := one_le_primeProductNorm p hp b'
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ Real.sqrt (primeProductNorm p a') * Real.sqrt (primeProductNorm p b') :=
                mul_le_mul (Real.one_le_sqrt.mpr h1) (Real.one_le_sqrt.mpr h2) zero_le_one
                  (Real.sqrt_nonneg _)
          have hCt : Cw / ((min 1 (Y / kernelDen p E a' b')) ^ 2 * (1 + T0) ^ At) ≤ Cl := by
            rw [hCl, ← div_div, div_eq_mul_inv Cw]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hCw) hP.le
          have hbn : bigGBound p hp hcop hg Ψ m f H g a' b' /
              ‖eisEmbedding (∏ i ∈ activeSupport a' b', p i)‖ ≤
                gSum ^ 2 * (‖H (g ∪ a')‖ * ‖H (g ∪ b')‖) :=
            (div_le_self hb0 hn1).trans hbB
          calc bigGBound p hp hcop hg Ψ m f H g a' b' /
                ‖eisEmbedding (∏ i ∈ activeSupport a' b', p i)‖ *
                (Cw / ((min 1 (Y / kernelDen p E a' b')) ^ 2 * (1 + T0) ^ At))
              ≤ gSum ^ 2 * (‖H (g ∪ a')‖ * ‖H (g ∪ b')‖) * Cl :=
                mul_le_mul hbn hCt (by positivity) (by positivity)
            _ = Cl * gSum ^ 2 * (‖H (g ∪ a')‖ * ‖H (g ∪ b')‖) := by ring
      _ = Cl * gSum ^ 2 * (∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖) ^ 2 := by
          rw [sq (∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖), Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.mul_sum]
  -- the pool-wide square bound
  have hL : ∀ g ∈ pool.powerset,
      (∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖) ^ 2 ≤
        128 * (bo * X) * ∑ U ∈ pool.powerset, ‖H U‖ ^ 2 := by
    intro g hgp
    refine (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (sum_sub_le pool g (fun U => ‖H U‖) (fun _ => norm_nonneg _)) 2).trans ?_
    rw [Finset.union_eq_left.mpr (Finset.mem_powerset.mp hgp)]
    exact sq_sum_live_le p pool (fun U => ‖H U‖) (bo * X)
      (fun U hU hne => Finset.mem_filter.mpr ⟨hU, hlive U (norm_ne_zero_iff.mp hne)⟩)
      (column_card_le p hp hinj pool (bo * X) hboX)
  set C1 := Y * (bo * X) * (Cl * gSum ^ 2 * (128 * (bo * X) * ∑ U ∈ pool.powerset, ‖H U‖ ^ 2))
    with hC1
  have hC10 : 0 ≤ C1 := by
    rw [hC1]
    apply mul_nonneg (mul_nonneg hY0 (by linarith))
    apply mul_nonneg (mul_nonneg hCl0 (sq_nonneg _))
    exact mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hterm : ∀ g ∈ pool.powerset,
      ∑ E ∈ g.powerset.attach,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
          ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) ball},
            ‖inner p hp hcop hg pool Ψ m f H Wk Y g E.1 k‖ ≤
        if primeProductNorm p g ≤ bo * X then C1 else 0 := by
    intro g hgp
    have hstep : ∑ E ∈ g.powerset.attach,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
          ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) ball},
            ‖inner p hp hcop hg pool Ψ m f H Wk Y g E.1 k‖ ≤
        (∑ E ∈ g.powerset.attach,
          Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2) *
          (Cl * gSum ^ 2 * (∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖) ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro E _
      exact mul_le_mul_of_nonneg_left (hgE g hgp E.1 E.2) (div_nonneg hY0 (sq_nonneg _))
    have hEs := sumE_le p hp g Y hY0
    have hEs0 : 0 ≤ ∑ E ∈ g.powerset.attach,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => div_nonneg hY0 (sq_nonneg _)
    split_ifs with hgl
    · refine hstep.trans ?_
      rw [hC1]
      apply mul_le_mul (hEs.trans (mul_le_mul_of_nonneg_left hgl hY0)) _ (by positivity)
        (mul_nonneg hY0 (by linarith))
      exact mul_le_mul_of_nonneg_left (hL g hgp) (mul_nonneg hCl0 (sq_nonneg _))
    · have hz : ∑ a' ∈ (pool \ g).powerset, ‖H (g ∪ a')‖ = 0 := by
        apply Finset.sum_eq_zero; intro a' ha'
        by_contra hne
        have hl := hlive _ (norm_ne_zero_iff.mp hne)
        have hga : Disjoint g a' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp ha')
          Finset.disjoint_sdiff
        rw [FirstPassCubeLabels.primeProductNorm_union p g a' hga] at hl
        have h1 := one_le_primeProductNorm p hp a'
        have h2 := FirstPassCubeLabels.primeProductNorm_pos p hp g
        apply hgl
        nlinarith
      refine hstep.trans (le_of_eq ?_)
      rw [hz]; ring
  calc _ ≤ ∑ g ∈ pool.powerset, (if primeProductNorm p g ≤ bo * X then C1 else 0) :=
        Finset.sum_le_sum hterm
    _ = ((pool.powerset.filter (fun g => primeProductNorm p g ≤ bo * X)).card : ℝ) * C1 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 128 * (bo * X) * C1 :=
        mul_le_mul_of_nonneg_right (column_card_le p hp hinj pool (bo * X) hboX) hC10
    _ = _ := by rw [hC1]; ring


end
end Qrh.MarkedAnchor.Inverse.Poisson
