/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterFixed

/-! Exact local algebra from supplied H9. These results retain the total
valuation cutoff i+j≤2 and independent coordinate deletions. They establish
local factors; they do not assert an infinite Euler-product or Mellin formula.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- The genuine cube-free local sum has the coupled valuation cutoff. -/
def cubeFreeLocal (x y : ℂ) : ℂ := 1+x+y+x^2+x*y+y^2

/-- The numerator in the supplied equation H9. -/
def cubeFreeNumerator (x y : ℂ) : ℂ :=
  1-(x^3+x^2*y+x*y^2+y^3)+(x^3*y+x^2*y^2+x*y^3)

theorem cubeFree_local_numerator (x y : ℂ) :
    (1-x)*(1-y)*cubeFreeLocal x y=cubeFreeNumerator x y := by
  unfold cubeFreeLocal cubeFreeNumerator
  ring

/-- Allowed residual valuations, including deletion of either or both variables.
A false keep flag forces residual valuation zero in that coordinate. -/
def residualPairs (keep₁ keep₂ : Bool) : Finset (ℕ×ℕ) :=
  ((Finset.range 3)×ˢ(Finset.range 3)).filter fun ij =>
    ij.1+ij.2 ≤ 2 ∧ (keep₁=true ∨ ij.1=0) ∧ (keep₂=true ∨ ij.2=0)

/-- The actual local character coefficients, without a character-value inverse.
Each character may already vanish on the prime through its original modulus. -/
def residualLocal (ψ₁ ψ₂ : Character) (P : Ideal O)
    (keep₁ keep₂ : Bool) (z₁ z₂ : ℂ) : ℂ :=
  ∑ ij ∈ residualPairs keep₁ keep₂,
    (idealCoeff ψ₁ P*z₁)^ij.1*(idealCoeff ψ₂ P*z₂)^ij.2

theorem residualLocal_eq (ψ₁ ψ₂ : Character) (P : Ideal O)
    (keep₁ keep₂ : Bool) (z₁ z₂ : ℂ) :
    residualLocal ψ₁ ψ₂ P keep₁ keep₂ z₁ z₂ =
      cubeFreeLocal (if keep₁ then idealCoeff ψ₁ P*z₁ else 0)
        (if keep₂ then idealCoeff ψ₂ P*z₂ else 0) := by
  cases keep₁ <;> cases keep₂ <;>
    norm_num [residualLocal,residualPairs,cubeFreeLocal,Finset.sum_range_succ,
      Finset.sum_filter,Finset.sum_product] <;> ring

/-- Deleting a prime from both ordinary variables leaves the literal constant 1. -/
theorem residualLocal_delete_both (ψ₁ ψ₂ : Character) (P : Ideal O) (z₁ z₂ : ℂ) :
    residualLocal ψ₁ ψ₂ P false false z₁ z₂=1 := by
  rw [residualLocal_eq]
  norm_num [cubeFreeLocal]

/-- One-coordinate deletion is handled by the true remaining cubic numerator. -/
theorem residualLocal_delete_first (ψ₁ ψ₂ : Character) (P : Ideal O) (z₁ z₂ : ℂ) :
    (1-idealCoeff ψ₂ P*z₂)*residualLocal ψ₁ ψ₂ P false true z₁ z₂=
      1-(idealCoeff ψ₂ P*z₂)^3 := by
  rw [residualLocal_eq]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  unfold cubeFreeLocal
  ring

theorem residualLocal_delete_second (ψ₁ ψ₂ : Character) (P : Ideal O) (z₁ z₂ : ℂ) :
    (1-idealCoeff ψ₁ P*z₁)*residualLocal ψ₁ ψ₂ P true false z₁ z₂=
      1-(idealCoeff ψ₁ P*z₁)^3 := by
  rw [residualLocal_eq]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  unfold cubeFreeLocal
  ring

/-- Clearing only the Euler factors that remain after coordinate deletion gives
H9 evaluated at the actual masked coefficients. No principal exception needed. -/
theorem residualLocal_cleared (ψ₁ ψ₂ : Character) (P : Ideal O)
    (keep₁ keep₂ : Bool) (z₁ z₂ : ℂ) :
    (1-(if keep₁ then idealCoeff ψ₁ P*z₁ else 0))*
      (1-(if keep₂ then idealCoeff ψ₂ P*z₂ else 0))*
      residualLocal ψ₁ ψ₂ P keep₁ keep₂ z₁ z₂ =
    cubeFreeNumerator (if keep₁ then idealCoeff ψ₁ P*z₁ else 0)
      (if keep₂ then idealCoeff ψ₂ P*z₂ else 0) := by
  rw [residualLocal_eq,cubeFree_local_numerator]

/-- The numerator starts at total degree three, uniformly in both characters. -/
theorem cubeFreeNumerator_error (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖cubeFreeNumerator x y-1‖ ≤ 7*r^3 := by
  have hxxx : ‖x^3‖ ≤ r^3 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx 3
  have hyyy : ‖y^3‖ ≤ r^3 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy 3
  have hxxy : ‖x^2*y‖ ≤ r^3 := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ r^2*r := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hy (norm_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hxyy : ‖x*y^2‖ ≤ r^3 := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ r*r^2 := mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg _) hy 2) (sq_nonneg _) hr
      _ = _ := by ring
  have h4 : r^3*r ≤ r^3 := by nlinarith [pow_nonneg hr 3]
  have hxxxy : ‖x^3*y‖ ≤ r^3 := by
    rw [norm_mul]
    exact (mul_le_mul hxxx hy (norm_nonneg _) (pow_nonneg hr 3)).trans h4
  have hxxyy : ‖x^2*y^2‖ ≤ r^3 := by
    rw [norm_mul,norm_pow,norm_pow]
    calc
      _ ≤ r^2*r^2 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2)
        (pow_le_pow_left₀ (norm_nonneg _) hy 2) (sq_nonneg _) (sq_nonneg _)
      _ = r^3*r := by ring
      _ ≤ _ := h4
  have hxyyy : ‖x*y^3‖ ≤ r^3 := by
    rw [norm_mul]
    calc
      _ ≤ r*r^3 := mul_le_mul hx hyyy (norm_nonneg _) hr
      _ = r^3*r := by ring
      _ ≤ _ := h4
  have htriangle : ‖cubeFreeNumerator x y-1‖ ≤
      ‖x^3‖+‖x^2*y‖+‖x*y^2‖+‖y^3‖+
        (‖x^3*y‖+‖x^2*y^2‖+‖x*y^3‖) := by
    have heq : cubeFreeNumerator x y-1 =
        -(x^3+x^2*y+x*y^2+y^3)+(x^3*y+x^2*y^2+x*y^3) := by
      unfold cubeFreeNumerator
      ring
    rw [heq]
    have h₁ := norm_add_le (x^3) (x^2*y)
    have h₂ := norm_add_le (x^3+x^2*y) (x*y^2)
    have h₃ := norm_add_le (x^3+x^2*y+x*y^2) (y^3)
    have h₄ := norm_add_le (x^3*y) (x^2*y^2)
    have h₅ := norm_add_le (x^3*y+x^2*y^2) (x*y^3)
    have h₆ := norm_add_le (-(x^3+x^2*y+x*y^2+y^3)) (x^3*y+x^2*y^2+x*y^3)
    rw [norm_neg] at h₆
    linarith
  nlinarith

/-- The same degree-three majorant applies with genuine character coefficients,
including any zeros forced by the original moduli and any supplying-prime holes. -/
theorem actual_masked_numerator_error (ψ₁ ψ₂ : Character) (P : Ideal O)
    (keep₁ keep₂ : Bool) (z₁ z₂ : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hz₁ : ‖z₁‖ ≤ r) (hz₂ : ‖z₂‖ ≤ r) :
    ‖cubeFreeNumerator (if keep₁ then idealCoeff ψ₁ P*z₁ else 0)
      (if keep₂ then idealCoeff ψ₂ P*z₂ else 0)-1‖ ≤ 7*r^3 := by
  apply cubeFreeNumerator_error _ _ r hr hr1
  · split_ifs
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one ψ₁ P) (norm_nonneg _)).trans (by simpa using hz₁)
    · simpa using hr
  · split_ifs
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one ψ₂ P) (norm_nonneg _)).trans (by simpa using hz₂)
    · simpa using hr

end
end QRH.Cycle092.SignedCenter
