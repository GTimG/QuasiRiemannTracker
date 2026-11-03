/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/ReflectedExponent.lean
Original SHA-256: 5e4e9272740edf5b79b88332e3f46182dfe6163ff7aeab72d452454ae73e3085
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reflected exponent with variable total slot width

The two scalar definitions below are exact transcriptions of
`OAI/NumberTheory/DirichletL/Inversion/TerminalWidths.lean:318–322`, from
OpenAI commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
The upstream license is preserved in `upstream-config/LICENSE`.

The proof extends the two-branch argument of
`OAI/NumberTheory/DirichletL/Detector/LowReflectedLength.lean` to total slot
width `E` and row width `1 - E`. It proves the exponent inequality itself;
it does not assume or assert a perturbed physical energy estimate.

These exact scalar formulas are isolated because the upstream file also
imports arithmetic infrastructure. The connection to an imported upstream
`reflectedExponent` is definitional, but this module does not import or build
that infrastructure.
-/

namespace LW56e2.Transport.Reflected

noncomputable section

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

def reflectedLoss (E d : ℝ) : ℝ := max 0 (5 * E - 1 + d) / 4

lemma hybrid_half_with_error {v za ε : ℝ} (hv : -ε ≤ v) (hε : 0 ≤ ε)
    (hu : hybridSaving v za ≠ za) : v / 2 - ε / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v + za) / 3)
      rw [min_eq_right hz] at hzv
      linarith

lemma retained_kernel_quarter (Td y : ℝ) :
    Td / 4 ≤ y / 4 + max 0 (Td - y) / 2 := by
  have h0 := le_max_left 0 (Td - y)
  have h1 := le_max_right 0 (Td - y)
  linarith

/-- The actual scalar exponent inequality, with row width `1-E` and selected
slot length at most `E-d`, allowing the source's small logarithmic errors. -/
theorem compensated_reflected_exponent_with_length
    (E d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀) (hH : H ≤ (1 - E - 2 * d) - O₀ + ε)
    (hA : 2 * A₀ ≤ O₀ + ε) (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hell : ell₀ ≤ E - d + ε) (hz : za ≤ ell₀ + ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el) (hθ : |θ| ≤ ε)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀ + ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀) ≤
        1 - E - 2 * d + reflectedLoss E d + 40 * ε := by
  let Td := 2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀
  have hθlo : -ε ≤ θ := (abs_le.mp hθ).1
  have hθhi : θ ≤ ε := (abs_le.mp hθ).2
  have hTd : Td ≤ H - 3 * d + 6 * ε := by
    dsimp [Td]
    linarith
  have hcol : v + ell ≤ H + 10 * ε := by
    dsimp [Td] at hTd
    linarith
  have hmax : max H (v + ell) ≤ H + 10 * ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td - v - 3 * ell - el)
  have hloss0 : 0 ≤ reflectedLoss E d := by
    unfold reflectedLoss
    exact div_nonneg (le_max_left _ _) (by norm_num)
  have hloss : (5 * E - 1 + d) / 4 ≤ reflectedLoss E d := by
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num)
  by_cases hu : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hu]
    change O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - za - ell -
      2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2 ≤ _
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v + 3 * ell + el)
    have hcharge : Td / 4 - 17 * ε / 12 ≤
        hybridSaving v za + ell + 2 * el / 3 +
          max 0 (Td - v - 3 * ell - el) / 2 := by
      have heq : Td - (v + 3 * ell + el) = Td - v - 3 * ell - el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        O₀ / 2 + H - S₀ - B₀ + za - Td / 4 + (10 + 17 / 12) * ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ _
    apply hbound.trans
    dsimp [Td]
    linarith

/-- A support-dependent compensation gain of `d/2` is more than sufficient
to absorb half the energy loss whenever the total slot width is at most `1/5`.
This is only the exponent comparison; the compensation sum still needs its
separate analytic proof. -/
theorem half_loss_absorbed_by_half_compensation {E d : ℝ}
    (hE : E ≤ 1 / 5) (hd : 0 ≤ d) :
    reflectedLoss E d / 2 - d / 2 ≤ -(3 * d / 8) := by
  have hm : max 0 (5 * E - 1 + d) ≤ d := max_le hd (by linarith)
  unfold reflectedLoss
  linarith

end

end LW56e2.Transport.Reflected
