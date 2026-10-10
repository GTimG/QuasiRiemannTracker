import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Retained-block exponent geometry for Appendix B.4. The exponent is the
proved reflection library's exponent, with its powerful-row cost counted once.
These lemmas do not assert the decomposition of the original theta sum. -/

namespace ZetaZeroFree.Analytic.Energy

noncomputable section
open OAI.SevenEighths.InverseTerminalWidths

def M : ℝ := 28 / 33
def z : ℝ := 5 / 33
def Nstar : ℝ := 38 / 33

def dualLength (H A za N B : ℝ) : ℝ :=
  2 * H + 2 * A + 2 * za - Nstar - N - 3 * B

theorem scale_balance : M + 2 * z - Nstar = 0 := by
  norm_num [M, z, Nstar]

theorem partial_margin : Nstar + 2 * z - 2 * M = -(8 / 33 : ℝ) := by
  norm_num [M, z, Nstar]

/-- B.22 implies that the retained dual range fits in the residual row range. -/
theorem dualLength_le_row {O H A za N B η : ℝ}
    (hH : H ≤ M - O + η) (hA : 2 * A ≤ O)
    (hza : za ≤ z) (hN : 0 ≤ N) (hB : 0 ≤ B) :
    dualLength H A za N B ≤ H + η := by
  have hb := scale_balance
  unfold dualLength
  linarith

/-- The lower bound preceding B.24, allowing the ramified width error. -/
theorem partial_absorption {v b el Td za η : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hel : -η ≤ el)
    (hu : hybridSaving v za ≠ za) :
    Td / 4 - 5 * η / 12 ≤
      hybridSaving v za + b + 2 * el / 3 + max 0 (Td - v - 3 * b - el) / 2 := by
  have hh := hybridSaving_half hv hu
  have hm := le_max_right 0 (Td - v - 3 * b - el)
  have h0 := le_max_left 0 (Td - v - 3 * b - el)
  linarith

/-- The quantitative inequality in B.24, before dropping local nonnegative costs. -/
theorem retained_partial_certificate {O H A S N B za v b el : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hel : 0 ≤ el)
    (hrow : v + b ≤ H) (hu : hybridSaving v za ≠ za) :
    4 * (reflectedExponent O H S B za v b el (dualLength H A za N B) - M) ≤
      Nstar + 2 * za - 2 * M - 2 * (M - O - H) -
        (2 * A - N + B + 4 * S) := by
  have ha := partial_absorption (Td := dualLength H A za N B) (η := 0)
    hv hb (by simpa using hel) hu
  unfold reflectedExponent
  rw [max_eq_left hrow]
  unfold dualLength at *
  linarith

/-- All small scale, frozen-support, and reflection-width errors are explicit. -/
theorem retained_block_bound_with_errors {O H A S N B za v b el Td η τ ρ σ ν : ℝ}
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hNA : N ≤ A) (hA : 2 * A ≤ O + ρ)
    (hza : za ≤ z + σ) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hel : -η ≤ el) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hH : H ≤ M - O + η)
    (hTdlo : dualLength H A za N B - ν ≤ Td)
    (hTdhi : Td ≤ dualLength H A za N B + ν)
    (hret : v + 3 * b + el ≤ Td + τ) :
    reflectedExponent O H S B za v b el Td ≤ M + 4 * η + ρ + 3 * σ + 2 * ν + τ := by
  have hbalance := scale_balance
  have hT : Td ≤ H + η + ρ + 2 * σ + ν := by
    unfold dualLength at hTdhi
    linarith
  have hr : v + b ≤ H + 2 * η + ρ + 2 * σ + ν + τ := by linarith
  have hm : max H (v + b) ≤ H + 2 * η + ρ + 2 * σ + ν + τ := by
    apply max_le
    · linarith
    · exact hr
  by_cases hu : hybridSaving v za = za
  · have h0 := le_max_left 0 (Td - v - 3 * b - el)
    unfold reflectedExponent
    rw [hu]
    linarith
  · have ha := partial_absorption (Td := Td) hv hb hel hu
    have hgap := partial_margin
    unfold reflectedExponent
    unfold dualLength at hTdlo
    linarith

/-- B.23--B.24 with retention and logarithmic-width buffers. -/
theorem retained_block_bound_buffered {O H A S N B za v b el η τ : ℝ}
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hNA : N ≤ A) (hA : 2 * A ≤ O)
    (hza : za ≤ z) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hel : -η ≤ el) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hH : H ≤ M - O + η)
    (hret : v + 3 * b + el ≤ dualLength H A za N B + τ) :
    reflectedExponent O H S B za v b el (dualLength H A za N B) ≤
      M + 4 * η + τ := by
  simpa using retained_block_bound_with_errors (ρ := 0) (σ := 0) (ν := 0)
    hO hS hB hN hNA (by simpa using hA) (by simpa using hza) hv hb hel hη hτ
    (by norm_num) (by norm_num) (by norm_num) hH (by simp) (by simp) hret

theorem retained_block_bound {O H A S N B za v b el : ℝ}
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hNA : N ≤ A) (hA : 2 * A ≤ O)
    (hza : za ≤ z) (hv : 0 ≤ v) (hb : 0 ≤ b) (hel : 0 ≤ el)
    (hH : H ≤ M - O)
    (hret : v + 3 * b + el ≤ dualLength H A za N B) :
    reflectedExponent O H S B za v b el (dualLength H A za N B) ≤ M := by
  simpa using retained_block_bound_buffered (η := 0) (τ := 0)
    hO hS hB hN hNA hA hza hv hb (by simpa using hel)
    (by norm_num) (by norm_num) (by simpa using hH) (by simpa using hret)

end
end ZetaZeroFree.Analytic.Energy
