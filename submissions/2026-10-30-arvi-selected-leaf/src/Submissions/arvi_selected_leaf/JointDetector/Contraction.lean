/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib

/-!
The finite exponent contraction used by the selected squarefree norm.
This module proves the scalar iteration and its uniform depth. It does not
postulate or prove the analytic reflection estimate.
-/

namespace Qrh.JointDetector.Contraction

noncomputable section

def ratio (δ : ℝ) : ℝ := (1 - δ) / δ

theorem ratio_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ ratio δ := div_nonneg (by linarith) hδ.le

theorem ratio_lt_one {δ : ℝ} (hδ : 1 / 2 < δ) : ratio δ < 1 := by
  have hpos : 0 < δ := by linarith
  exact (div_lt_one hpos).2 (by linarith)

theorem ratio_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ratio b ≤ ratio a := by
  have hb : 0 < b := ha.trans_le hab
  unfold ratio
  apply (div_le_div_iff₀ hb ha).2
  nlinarith

def exponent (δ : ℝ) : ℕ → ℝ
  | 0 => 1 + δ
  | n + 1 => 2 * δ - 1 + ratio δ * exponent δ n

theorem exponent_eq (δ : ℝ) (hδ : δ ≠ 0) (n : ℕ) :
    exponent δ n = δ + ratio δ ^ n := by
  have hr : ratio δ * δ = 1 - δ := div_mul_cancel₀ _ hδ
  induction n with
  | zero => simp [exponent, add_comm]
  | succ n ih =>
    rw [exponent, ih, mul_add, hr, pow_succ]
    ring

/-- Choose the contraction depth before the eventual finite slot data:
the same depth works for the full closed slope range above a fixed gap. -/
theorem uniform_depth {η ε : ℝ} (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hε : 0 < ε) :
    ∃ n : ℕ, ∀ δ : ℝ, 1 / 2 + η ≤ δ → δ ≤ 3 / 4 →
      exponent δ n < δ + ε := by
  have hbase : 0 < (1 / 2 : ℝ) + η := by linarith
  have hr0 : 0 ≤ ratio ((1 / 2 : ℝ) + η) :=
    ratio_nonneg hbase (by linarith)
  have hr1 : ratio ((1 / 2 : ℝ) + η) < 1 := ratio_lt_one (by linarith)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr1
  refine ⟨n, ?_⟩
  intro δ hlo hhi
  have hδ : 0 < δ := hbase.trans_le hlo
  have hδ0 : 0 ≤ ratio δ := ratio_nonneg hδ (by linarith)
  have hle : ratio δ ≤ ratio ((1 / 2 : ℝ) + η) := ratio_antitone hbase hlo
  have hp : ratio δ ^ n ≤ ratio ((1 / 2 : ℝ) + η) ^ n :=
    pow_le_pow_left₀ hδ0 hle n
  rw [exponent_eq δ hδ.ne' n]
  linarith

/-- Inserting the trivial row/column cardinality estimate into reflection
already yields the additive starting scale; a separate sextic additive
sieve theorem is unnecessary once reflection has been proved. -/
theorem reflected_trivial_identity (L B D R : ℝ)
    (hL : L ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hR : R ≠ 0) :
    (L * D / (B * R)) * (B / D) * (B ^ 2 * R / (L * D ^ 2)) =
      B ^ 2 / D ^ 2 := by
  field_simp

theorem reflected_trivial_le (L B D R : ℝ)
    (hL : 0 < L) (hB : 0 < B) (hD : 1 ≤ D) (hR : 1 ≤ R) :
    L / R + (L * D / (B * R)) * (B / D) *
        (B ^ 2 * R / (L * D ^ 2)) ≤ L + B ^ 2 := by
  have hDpos : 0 < D := by linarith
  have hRpos : 0 < R := by linarith
  rw [reflected_trivial_identity L B D R hL.ne' hB.ne' hDpos.ne' hRpos.ne']
  apply add_le_add
  · exact div_le_self hL.le hR
  · exact div_le_self (sq_nonneg B) (by nlinarith)

end

end Qrh.JointDetector.Contraction
