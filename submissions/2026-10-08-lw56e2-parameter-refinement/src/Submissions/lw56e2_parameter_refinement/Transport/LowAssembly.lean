/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/LowAssembly.lean
Original SHA-256: 98c1115a5de4bfb1ac4edce489126d57388e4029c111adcec02904dbc6bf1db0
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.ReflectedExponent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite low-pairing assembly at a variable row width

This module performs the Cauchy--Schwarz and compensation step of the low
argument. The row pairing is an actual finite complex sum. Its two separate
energy bounds and the support-sensitive compensation mass remain hypotheses;
this is not a producer of those arithmetic estimates or of a physical probe.

The first proof follows the unchanged finite Cauchy argument in OpenAI's
`Moments/Cauchy.lean`, at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (license in
`upstream-config/LICENSE`). Squared amplitude constants in the main theorem
are simply a convenient way of stating nonnegative energy bounds.
-/

namespace LW56e2.Transport.LowAssembly

noncomputable section
open scoped BigOperators

theorem finite_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

theorem finite_row_bound {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) {a b : ℝ}
    (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∑ k ∈ rows, ‖A k‖ ^ 2 ≤ a ^ 2)
    (hB : ∑ k ∈ rows, ‖B k‖ ^ 2 ≤ b ^ 2) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤ a * b := by
  apply (finite_row_cauchy rows w A B hw).trans
  exact mul_le_mul (Real.sqrt_le_iff.mpr ⟨ha, hA⟩)
    (Real.sqrt_le_iff.mpr ⟨hb, hB⟩) (Real.sqrt_nonneg _) ha

/-- Combining separate Gram and reflected energies with support-sensitive
compensation mass. Here `q` is the compensated row-width exponent, `g i` is
the tuple-dependent Gram amplitude, and `ε` is the retained analytic error.
No bound on the final pairing is assumed. -/
theorem compensated_low_pairing {ι κ : Type*}
    (tuples : Finset ι) (rows : ι → Finset κ)
    (weight : ι → ℂ) (w A B : ι → κ → ℂ) (g : ι → ℝ)
    {Z E d q L ε Cg Ce Cm : ℝ}
    (hZ : 1 ≤ Z) (hE : E ≤ 1 / 5) (hd : 0 ≤ d)
    (hCg : 0 ≤ Cg) (hCe : 0 ≤ Ce) (hCm : 0 ≤ Cm)
    (hg : ∀ i ∈ tuples, 0 ≤ g i)
    (hw : ∀ i ∈ tuples, ∀ k ∈ rows i, ‖w i k‖ ≤ 1)
    (hGram : ∀ i ∈ tuples,
      ∑ k ∈ rows i, ‖A i k‖ ^ 2 ≤ (Cg * g i * Z ^ L) ^ 2)
    (hEnergy : ∀ i ∈ tuples,
      ∑ k ∈ rows i, ‖B i k‖ ^ 2 ≤
        (Ce * Z ^ ((q + Reflected.reflectedLoss E d) / 2 + ε)) ^ 2)
    (hMass : ∑ i ∈ tuples, ‖weight i‖ * g i ≤ Cm * Z ^ (-d / 2)) :
    ‖∑ i ∈ tuples, weight i * (Z ^ (-q / 2) : ℝ) *
      (∑ k ∈ rows i, w i k * A i k * B i k)‖ ≤
        (Cg * Ce * Cm) * Z ^ (L + ε - 3 * d / 8) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (x : ℝ) : 0 ≤ Z ^ x := Real.rpow_nonneg hZ0.le x
  have hrow (i : ι) (hi : i ∈ tuples) :
      ‖∑ k ∈ rows i, w i k * A i k * B i k‖ ≤
        (Cg * g i * Z ^ L) *
          (Ce * Z ^ ((q + Reflected.reflectedLoss E d) / 2 + ε)) :=
    finite_row_bound (rows i) (w i) (A i) (B i) (hw i hi)
      (mul_nonneg (mul_nonneg hCg (hg i hi)) (hp L))
      (mul_nonneg hCe (hp _)) (hGram i hi) (hEnergy i hi)
  let F := Cg * Ce * Z ^ (L + Reflected.reflectedLoss E d / 2 + ε)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg hCg hCe) (hp _)
  have hterm (i : ι) (hi : i ∈ tuples) :
      ‖weight i * (Z ^ (-q / 2) : ℝ) *
        (∑ k ∈ rows i, w i k * A i k * B i k)‖ ≤
          (‖weight i‖ * g i) * F := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp _)]
    apply (mul_le_mul_of_nonneg_left (hrow i hi)
      (mul_nonneg (norm_nonneg _) (hp _))).trans_eq
    dsimp [F]
    have he : -q / 2 + L + ((q + Reflected.reflectedLoss E d) / 2 + ε) =
        L + Reflected.reflectedLoss E d / 2 + ε := by ring
    rw [← he, Real.rpow_add hZ0 (-q / 2 + L)
      ((q + Reflected.reflectedLoss E d) / 2 + ε),
      Real.rpow_add hZ0 (-q / 2) L]
    ring
  calc
    _ ≤ ∑ i ∈ tuples, ‖weight i * (Z ^ (-q / 2) : ℝ) *
          (∑ k ∈ rows i, w i k * A i k * B i k)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ tuples, (‖weight i‖ * g i) * F :=
      Finset.sum_le_sum hterm
    _ = (∑ i ∈ tuples, ‖weight i‖ * g i) * F :=
      (Finset.sum_mul ..).symm
    _ ≤ (Cm * Z ^ (-d / 2)) * F := mul_le_mul_of_nonneg_right hMass hF
    _ = (Cg * Ce * Cm) *
        Z ^ (L + ε + (Reflected.reflectedLoss E d / 2 - d / 2)) := by
      dsimp [F]
      have he : L + ε + (Reflected.reflectedLoss E d / 2 - d / 2) =
          -d / 2 + (L + Reflected.reflectedLoss E d / 2 + ε) := by ring
      rw [he, Real.rpow_add hZ0 (-d / 2)
        (L + Reflected.reflectedLoss E d / 2 + ε)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by
        have h := Reflected.half_loss_absorbed_by_half_compensation hE hd
        linarith)) (mul_nonneg (mul_nonneg hCg hCe) hCm)

end
end LW56e2.Transport.LowAssembly
