/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.CellBound

/-!
# Inverse.Poisson.LamLabel — the `t`-density of one label by cell integrals

`labelLam ≤ ∑_{χ,η} |cc| ∑_{t' ⊆ pool, N t' ≤ 2 bo X} K₁/N t' ∑_c |gCoeff c.1| (FA_c + FB_c)`,
`FA_c = ∫ |b'| ‖child_{χ,c,t'}(τ + s₀ + t)(-y)‖²`, `FB_c = ∫ |b'| ‖child_{η,c,t'}(τ + s₀ - t)(y)‖²`,
`K₁ = Gs · 2^#slots · Lp² · ∫|b'| / 2`.

The cell integrals are gated by `cellOK` (the frozen slots `c.2` carry an injective tuple `d`
with `Xc · ∏ N(d_i) ≤ 2X`, `Xc = X/(2^i N t')`): a cell whose weight `|mark_{c.2}(g ∪ t')|` is
nonzero satisfies it (`cellOK_of_cellW_ne`, from `N g ≤ 2·2^i`), so `lamTerm` uses the gated
cell `cellG = [cellOK] · cellF`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
open OAI.ConcreteTraceCRT (eisEmbedding)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The cell integral of one side. -/
def cellF (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X h : ℝ) (c : RayCharacter × Finset σ)
    (i : ℕ) (z : O) : ℝ :=
  ∫ τ : ℝ, ‖b' τ‖ * cellChild p hg pool t ψ₀ m slots lists a Φ
    (X / (2 ^ i * primeProductNorm p t)) h z c τ ^ 2

theorem cellF_nonneg (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X h : ℝ)
    (c : RayCharacter × Finset σ) (i : ℕ) (z : O) :
    0 ≤ cellF p hg pool t ψ₀ m slots lists a Φ b' X h c i z :=
  integral_nonneg fun τ => by positivity

/-- The child hypothesis is applicable to the cell `(i, t, J)`: an injective `J`-tuple pays the
frozen slots, `Xc · ∏ N(d_k) ≤ 2X` with `Xc = X/(2^i N t)`. -/
def cellOK (lists : σ → Finset ι) (X : ℝ) (i : ℕ) (t : Finset ι) (J : Finset σ) : Prop :=
  ∃ d ∈ injPi J lists, X / (2 ^ i * primeProductNorm p t) *
    ∏ k ∈ J.attach, ‖eisEmbedding (p (d k.1 k.2))‖ ^ 2 ≤ 2 * X

/-- The gated cell integral. -/
def cellG (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X h : ℝ) (c : RayCharacter × Finset σ)
    (i : ℕ) (z : O) : ℝ :=
  if cellOK p lists X i t c.2 then cellF p hg pool t ψ₀ m slots lists a Φ b' X h c i z else 0

theorem cellG_nonneg (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X h : ℝ)
    (c : RayCharacter × Finset σ) (i : ℕ) (z : O) :
    0 ≤ cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i z := by
  unfold cellG
  split_ifs
  · exact cellF_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i z
  · exact le_rfl

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem primeProductNorm_eq_prod_sq (A : Finset ι) :
    primeProductNorm p A = ∏ x ∈ A, ‖eisEmbedding (p x)‖ ^ 2 := by
  simp only [primeProductNorm, map_prod, norm_prod, Finset.prod_pow]

include hp in
/-- An injective tuple into `U` has norm product `≤ N U`. -/
theorem prod_injPi_le (J : Finset σ) (lists : σ → Finset ι) (U : Finset ι) (d : ∀ k ∈ J, ι)
    (hd : d ∈ injPi J lists) (hU : ∀ k ∈ J.attach, d k.1 k.2 ∈ U) :
    ∏ k ∈ J.attach, ‖eisEmbedding (p (d k.1 k.2))‖ ^ 2 ≤ primeProductNorm p U := by
  set img := J.attach.image (fun k => d k.1 k.2) with himg
  have hinj : ∀ k₁ ∈ J.attach, ∀ k₂ ∈ J.attach, d k₁.1 k₁.2 = d k₂.1 k₂.2 → k₁ = k₂ :=
    fun k₁ _ k₂ _ h => Subtype.ext ((mem_injPi.mp hd).2 k₁.1 k₁.2 k₂.1 k₂.2 h)
  have h1 : ∏ k ∈ J.attach, ‖eisEmbedding (p (d k.1 k.2))‖ ^ 2 = primeProductNorm p img := by
    rw [primeProductNorm_eq_prod_sq, himg, Finset.prod_image hinj]
  have hsub : img ⊆ U := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact hU k hk
  have h2 : primeProductNorm p U = primeProductNorm p img * primeProductNorm p (U \ img) := by
    rw [← FirstPassCubeLabels.primeProductNorm_union p img (U \ img) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hsub]
  rw [h1, h2]
  have := one_le_primeProductNorm p hp (U \ img)
  have := FirstPassCubeLabels.primeProductNorm_pos p hp img
  nlinarith

include hp in
/-- A cell with nonzero weight is admissible for the child hypothesis. -/
theorem cellOK_of_cellW_ne (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (g t : Finset ι) (X : ℝ) (i : ℕ) (hX : 0 < X) (hgt : Disjoint g t)
    (hgi : primeProductNorm p g ≤ 2 * 2 ^ i) (J : Finset σ)
    (hW : primeMarkInj J lists a (g ∪ t) ≠ 0) : cellOK p lists X i t J := by
  obtain ⟨d, hd, hU⟩ := exists_injPi_of_markInj_ne_zero J lists a (g ∪ t) hW
  refine ⟨d, hd, ?_⟩
  have hprod := prod_injPi_le p hp J lists (g ∪ t) d hd hU
  rw [FirstPassCubeLabels.primeProductNorm_union p g t hgt] at hprod
  have hNt := FirstPassCubeLabels.primeProductNorm_pos p hp t
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  have hXc : 0 ≤ X / (2 ^ i * primeProductNorm p t) := by positivity
  calc X / (2 ^ i * primeProductNorm p t) * ∏ k ∈ J.attach, ‖eisEmbedding (p (d k.1 k.2))‖ ^ 2
      ≤ X / (2 ^ i * primeProductNorm p t) * (primeProductNorm p g * primeProductNorm p t) :=
        mul_le_mul_of_nonneg_left hprod hXc
    _ = X * primeProductNorm p g / 2 ^ i := by field_simp
    _ ≤ X * (2 * 2 ^ i) / 2 ^ i := by gcongr
    _ = 2 * X := by field_simp

/-- The label constant `K₁`. -/
def kOne (slots : Finset σ) (Lp : ℝ) (b' : 𝓢(ℝ, ℂ)) : ℝ :=
  (∑ θ : RayCharacter, ‖gCoeff θ‖) * ((slots.powerset.card : ℝ) * Lp) * Lp *
    (∫ τ : ℝ, ‖b' τ‖) / 2

theorem cellW_le (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (g t : Finset ι)
    (Lp : ℝ) (hLp : ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t)‖ ≤ Lp)
    (c : RayCharacter × Finset σ) (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset) :
    cellW p slots lists a g t c ≤ ‖gCoeff c.1‖ * Lp * (Real.sqrt (primeProductNorm p t))⁻¹ := by
  unfold cellW
  have := hLp c.2 (Finset.mem_product.mp hc).2
  gcongr

theorem cellSW_le (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (g t : Finset ι)
    (b' : 𝓢(ℝ, ℂ)) (Lp : ℝ) (hLp : ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t)‖ ≤ Lp) :
    cellSW p slots lists a g t b' ≤
      (∑ θ : RayCharacter, ‖gCoeff θ‖) * ((slots.powerset.card : ℝ) * Lp) *
        (Real.sqrt (primeProductNorm p t))⁻¹ * ∫ τ : ℝ, ‖b' τ‖ := by
  unfold cellSW
  have hI : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ := integral_nonneg fun τ => norm_nonneg _
  calc ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        cellW p slots lists a g t c * ∫ τ : ℝ, ‖b' τ‖
      ≤ ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        ‖gCoeff c.1‖ * Lp * (Real.sqrt (primeProductNorm p t))⁻¹ * ∫ τ : ℝ, ‖b' τ‖ :=
        Finset.sum_le_sum fun c hc =>
          mul_le_mul_of_nonneg_right (cellW_le p slots lists a g t Lp hLp c hc) hI
    _ = _ := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
        ring

include hp in
theorem cellW_mul_le_gate (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (g t : Finset ι) (X : ℝ) (i : ℕ) (hX : 0 < X) (hgt : Disjoint g t)
    (hgi : primeProductNorm p g ≤ 2 * 2 ^ i) (Lp : ℝ)
    (hLp : ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t)‖ ≤ Lp)
    (c : RayCharacter × Finset σ) (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (F : ℝ) (hF : 0 ≤ F) :
    cellW p slots lists a g t c * F ≤
      ‖gCoeff c.1‖ * Lp * (Real.sqrt (primeProductNorm p t))⁻¹ *
        (if cellOK p lists X i t c.2 then F else 0) := by
  by_cases hok : cellOK p lists X i t c.2
  · rw [if_pos hok]
    exact mul_le_mul_of_nonneg_right (cellW_le p slots lists a g t Lp hLp c hc) hF
  · rw [if_neg hok, mul_zero]
    have hz : primeMarkInj c.2 lists a (g ∪ t) = 0 := by
      by_contra hne
      exact hok (cellOK_of_cellW_ne p hp lists a g t X i hX hgt hgi c.2 hne)
    unfold cellW
    rw [hz, norm_zero, mul_zero, zero_mul, zero_mul]

include hp in
theorem cellSq_le_gate (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (X h : ℝ) (i : ℕ) (z : O) (Lp : ℝ) (hX : 0 < X) (hgt : Disjoint g t)
    (hgi : primeProductNorm p g ≤ 2 * 2 ^ i)
    (hLp : ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t)‖ ≤ Lp) :
    cellSq p hg pool t ψ₀ m slots lists a Φ b' g (X / (2 ^ i * primeProductNorm p t)) h z ≤
      ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        ‖gCoeff c.1‖ * Lp * (Real.sqrt (primeProductNorm p t))⁻¹ *
          cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i z := by
  unfold cellSq cellG
  exact Finset.sum_le_sum fun c hc => cellW_mul_le_gate p hp slots lists a g t X i hX hgt hgi Lp
    hLp c hc _ (cellF_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i z)

theorem cellSq_le (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (X h : ℝ) (i : ℕ) (z : O) (Lp : ℝ)
    (hLp : ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t)‖ ≤ Lp) :
    cellSq p hg pool t ψ₀ m slots lists a Φ b' g (X / (2 ^ i * primeProductNorm p t)) h z ≤
      ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
        ‖gCoeff c.1‖ * Lp * (Real.sqrt (primeProductNorm p t))⁻¹ *
          cellF p hg pool t ψ₀ m slots lists a Φ b' X h c i z := by
  unfold cellSq
  exact Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_right
    (cellW_le p slots lists a g t Lp hLp c hc) (cellF_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i z)

include hp in
theorem cellSq_zero_large (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (bo X h : ℝ) (i : ℕ) (z : O) (hX : 0 < X) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (ht : 2 * bo * X < primeProductNorm p t) :
    cellSq p hg pool t ψ₀ m slots lists a Φ b' g (X / (2 ^ i * primeProductNorm p t)) h z = 0 := by
  unfold cellSq cellChild
  apply Finset.sum_eq_zero
  intro c _
  simp only [childRow_zero_large p hp hg pool t _ m _ lists a Φ bo X i _ z hX hΦ ht, norm_zero]
  simp

theorem cellSq_nonneg (pool t : Finset ι) (ψ₀ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (Xc h : ℝ) (z : O) :
    0 ≤ cellSq p hg pool t ψ₀ m slots lists a Φ b' g Xc h z := by
  unfold cellSq cellW
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity)
    (integral_nonneg fun τ => by positivity)

theorem cellSW_nonneg (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (g t : Finset ι)
    (b' : 𝓢(ℝ, ℂ)) : 0 ≤ cellSW p slots lists a g t b' := by
  unfold cellSW cellW
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity)
    (integral_nonneg fun τ => norm_nonneg _)

/-- The right side of one `t'`-term. -/
def lamTerm (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X : ℝ) (i : ℕ) (s₀ : ℝ) (y : O) (t : ℝ)
    (Lp : ℝ) (χ η : RayCharacter) (t' : Finset ι) : ℝ :=
  kOne slots Lp b' / primeProductNorm p t' *
    ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ *
      (cellG p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' X (s₀ + t) c i (-y) +
        cellG p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' X (s₀ - t) c i y)

include hp in
theorem lamTerm_nonneg (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (X : ℝ) (i : ℕ)
    (s₀ : ℝ) (y : O) (t Lp : ℝ) (hLp0 : 0 ≤ Lp) (χ η : RayCharacter) (t' : Finset ι) :
    0 ≤ lamTerm p hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp χ η t' := by
  unfold lamTerm
  have hIb : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ := integral_nonneg fun τ => norm_nonneg _
  apply mul_nonneg
  · unfold kOne
    have := FirstPassCubeLabels.primeProductNorm_pos p hp t'
    have : 0 ≤ ∑ θ : RayCharacter, ‖gCoeff θ‖ := Finset.sum_nonneg fun θ _ => norm_nonneg _
    positivity
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _)
      (add_nonneg (cellG_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i _)
        (cellG_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i _))

include hp in
theorem lam_term_le (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (X : ℝ) (i : ℕ) (s₀ : ℝ) (y : O) (t : ℝ) (bo Lp : ℝ) (hX : 0 < X)
    (hΦ : ∀ x, 2 * bo < x → Φ x = 0) (χ η : RayCharacter) (t' : Finset ι)
    (hgt : Disjoint g t') (hgi : primeProductNorm p g ≤ 2 * 2 ^ i)
    (hL : primeProductNorm p t' ≤ 2 * bo * X →
      ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t')‖ ≤ Lp) :
    (1 / 2 : ℝ) *
        (cellSW p slots lists a g t' b' *
            cellSq p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' g
              (X / (2 ^ i * primeProductNorm p t')) (s₀ + t) (-y) +
          cellSW p slots lists a g t' b' *
            cellSq p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' g
              (X / (2 ^ i * primeProductNorm p t')) (s₀ - t) y) ≤
      if primeProductNorm p t' ≤ 2 * bo * X then
        lamTerm p hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp χ η t' else 0 := by
  split_ifs with hN
  · have hL' := hL hN
    have hNt := FirstPassCubeLabels.primeProductNorm_pos p hp t'
    have hsq : (Real.sqrt (primeProductNorm p t'))⁻¹ * (Real.sqrt (primeProductNorm p t'))⁻¹ =
        1 / primeProductNorm p t' := by
      rw [← mul_inv, Real.mul_self_sqrt hNt.le, one_div]
    have hSW := cellSW_le p slots lists a g t' b' Lp hL'
    have hA := cellSq_le_gate p hp hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' g X
      (s₀ + t) i (-y) Lp hX hgt hgi hL'
    have hB := cellSq_le_gate p hp hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' g X
      (s₀ - t) i y Lp hX hgt hgi hL'
    have hA0 := cellSq_nonneg p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' g
      (X / (2 ^ i * primeProductNorm p t')) (s₀ + t) (-y)
    have hB0 := cellSq_nonneg p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' g
      (X / (2 ^ i * primeProductNorm p t')) (s₀ - t) y
    have hSW0 := cellSW_nonneg p slots lists a g t' b'
    have hSWb : 0 ≤ (∑ θ : RayCharacter, ‖gCoeff θ‖) * ((slots.powerset.card : ℝ) * Lp) *
        (Real.sqrt (primeProductNorm p t'))⁻¹ * ∫ τ : ℝ, ‖b' τ‖ := hSW0.trans hSW
    refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hSW hA hA0 hSWb)
      (mul_le_mul hSW hB hB0 hSWb)) (by norm_num)).trans (le_of_eq ?_)
    simp only [lamTerm, kOne, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    set sq := (Real.sqrt (primeProductNorm p t'))⁻¹ with hsqdef
    have hN' : primeProductNorm p t' = (sq * sq)⁻¹ := by rw [hsq, one_div, inv_inv]
    rw [hN']
    simp only [div_eq_mul_inv, inv_inv]
    ring
  · have hgt : 2 * bo * X < primeProductNorm p t' := lt_of_not_ge hN
    rw [cellSq_zero_large p hp hg pool t' _ m slots lists a Φ b' g bo X (s₀ + t) i (-y) hX hΦ hgt,
      cellSq_zero_large p hp hg pool t' _ m slots lists a Φ b' g bo X (s₀ - t) i y hX hΦ hgt]
    simp

include hp in
theorem lam_label_le (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (g : Finset ι)
    (X : ℝ) (i : ℕ) (s₀ : ℝ) (y : O) (t : ℝ) (bo Lp : ℝ) (hX : 0 < X)
    (hΦ : ∀ x, 2 * bo < x → Φ x = 0) (hLp0 : 0 ≤ Lp) (hgi : primeProductNorm p g ≤ 2 * 2 ^ i)
    (hLp : ∀ t' ∈ (pool \ g).powerset, primeProductNorm p t' ≤ 2 * bo * X →
      ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (g ∪ t')‖ ≤ Lp) :
    labelLam p hg pool Ψ m slots lists a Φ b' g X i s₀ y t ≤
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖ *
        ∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          lamTerm p hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp χ η t' := by
  unfold labelLam
  apply Finset.sum_le_sum; intro χ _
  apply Finset.sum_le_sum; intro η _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc _ ≤ ∑ t' ∈ (pool \ g).powerset,
          (if primeProductNorm p t' ≤ 2 * bo * X then
            lamTerm p hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp χ η t' else 0) :=
        Finset.sum_le_sum fun t' ht' => lam_term_le p hp hg pool Ψ m slots lists a Φ b' g X i s₀
          y t bo Lp hX hΦ χ η t' (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp ht')
            Finset.disjoint_sdiff) hgi (hLp t' ht')
    _ = ∑ t' ∈ (pool \ g).powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          lamTerm p hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp χ η t' :=
        (Finset.sum_filter _ _).symm
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset_filter _ (Finset.powerset_mono.mpr Finset.sdiff_subset)
        · intro t' _ _
          exact lamTerm_nonneg p hp hg pool Ψ m slots lists a Φ b' X i s₀ y t Lp hLp0 χ η t'

end
end Qrh.MarkedAnchor.Inverse.Poisson
