/- A48 (AI-assisted, for liqsweep): product-form tensor Bernstein certificates.
Released under Apache 2.0, like the Cycle61 source it extends. -/
import Mathlib.Tactic

set_option autoImplicit false

namespace Cycle61.CountAffine

/-- One product-form Bernstein term on a box `[a,b] × [c,e]`. -/
noncomputable def bterm (n₁ n₂ i j : ℕ) (a b c e δ p : ℝ) : ℝ :=
  (δ - a)^i * (b - δ)^(n₁ - i) * (p - c)^j * (e - p)^(n₂ - j)

theorem bterm_nonneg {n₁ n₂ i j : ℕ} {a b c e δ p : ℝ}
    (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc c e) : 0 ≤ bterm n₁ n₂ i j a b c e δ p := by
  have h1 : 0 ≤ δ - a := by linarith [hδ.1]
  have h2 : 0 ≤ b - δ := by linarith [hδ.2]
  have h3 : 0 ≤ p - c := by linarith [hp.1]
  have h4 : 0 ≤ e - p := by linarith [hp.2]
  unfold bterm
  positivity

/-- A certificate polynomial: `m + Σ g i j * bterm i j`. -/
noncomputable def bsum (n₁ n₂ : ℕ) (m : ℝ) (g : Fin (n₁+1) → Fin (n₂+1) → ℝ)
    (a b c e δ p : ℝ) : ℝ :=
  m + ∑ i, ∑ j, g i j * bterm n₁ n₂ i j a b c e δ p

theorem bsum_pos {n₁ n₂ : ℕ} {m : ℝ} {g : Fin (n₁+1) → Fin (n₂+1) → ℝ}
    {a b c e δ p : ℝ} (hm : 0 < m) (hg : ∀ i j, 0 ≤ g i j)
    (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc c e) :
    0 < bsum n₁ n₂ m g a b c e δ p := by
  unfold bsum
  have hs : 0 ≤ ∑ i, ∑ j, g i j * bterm n₁ n₂ i j a b c e δ p := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hg i j) (bterm_nonneg hδ hp)
  linarith

theorem bsum_nonneg {n₁ n₂ : ℕ} {m : ℝ} {g : Fin (n₁+1) → Fin (n₂+1) → ℝ}
    {a b c e δ p : ℝ} (hm : 0 ≤ m) (hg : ∀ i j, 0 ≤ g i j)
    (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc c e) :
    0 ≤ bsum n₁ n₂ m g a b c e δ p := by
  unfold bsum
  have hs : 0 ≤ ∑ i, ∑ j, g i j * bterm n₁ n₂ i j a b c e δ p := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hg i j) (bterm_nonneg hδ hp)
  linarith

/-- Univariate product-form certificate on `[a,b]`. -/
noncomputable def usum (n : ℕ) (m : ℝ) (g : Fin (n+1) → ℝ) (a b δ : ℝ) : ℝ :=
  m + ∑ i, g i * ((δ - a)^(i:ℕ) * (b - δ)^(n - i))

theorem usum_pos {n : ℕ} {m : ℝ} {g : Fin (n+1) → ℝ} {a b δ : ℝ}
    (hm : 0 < m) (hg : ∀ i, 0 ≤ g i) (hδ : δ ∈ Set.Icc a b) :
    0 < usum n m g a b δ := by
  unfold usum
  have h1 : 0 ≤ δ - a := by linarith [hδ.1]
  have h2 : 0 ≤ b - δ := by linarith [hδ.2]
  have hs : 0 ≤ ∑ i, g i * ((δ - a)^(i:ℕ) * (b - δ)^(n - i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hg i) (by positivity)
  linarith

end Cycle61.CountAffine
