/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss

def sourceLine (a b x : ℝ) : ℝ := a - b * x

/-- A steeper descending affine line that is lower at a boundary remains
lower throughout the half-line to its right. -/
theorem sourceLine_nesting {a b a' b' c x : ℝ}
    (hslope : b ≤ b') (hboundary : sourceLine a' b' c ≤ sourceLine a b c)
    (hx : c ≤ x) : sourceLine a' b' x ≤ sourceLine a b x := by
  unfold sourceLine at *
  nlinarith [mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hx)]

/-- Adjacent output comparisons and nested affine source lines imply every
earlier-stage minorant. The certificate therefore needs linear work in the
number of stages, rather than a separate check for every ordered stage pair. -/
theorem all_earlier_minorants (N : ℕ) (R a b : ℕ → ℝ) (Y : ℕ → ℝ → ℝ)
    (pad : ℝ) (hR : Antitone R)
    (hadj : ∀ i, i + 1 < N → ∀ x, R (i + 1) ≤ x → x ≤ R i →
      sourceLine (a (i + 1)) (b (i + 1)) x + pad < Y i x)
    (hslope : ∀ i, i + 1 < N → b i ≤ b (i + 1))
    (hboundary : ∀ i, i + 1 < N →
      sourceLine (a (i + 1)) (b (i + 1)) (R i) ≤ sourceLine (a i) (b i) (R i)) :
    ∀ i, i < N → ∀ j, j < i → ∀ x, R (j + 1) ≤ x → x ≤ R j →
      sourceLine (a i) (b i) x + pad < Y j x := by
  intro i
  induction i with
  | zero => intros; omega
  | succ i ih =>
    intro hi j hj x hlo hhi
    by_cases heq : j = i
    · subst j
      exact hadj i hi x hlo hhi
    · have hji : j < i := by omega
      have hix : R i ≤ x := (hR (show j + 1 ≤ i by omega)).trans hlo
      have hn := sourceLine_nesting (hslope i hi) (hboundary i hi) hix
      have hp := ih (by omega) j hji x hlo hhi
      linarith

end Qrh.TwoSlot.AnchorZeroLoss

#print axioms Qrh.TwoSlot.AnchorZeroLoss.all_earlier_minorants
