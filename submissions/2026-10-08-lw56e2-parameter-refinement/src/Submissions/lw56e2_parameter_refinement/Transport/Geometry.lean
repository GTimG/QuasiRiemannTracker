/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/Geometry.lean
Original SHA-256: fc41523709550a747dbdc48128745c82979d5586c48b496077322d1a8871b4b8
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebra of the perturbed compensated-probe geometry

This module is independently authored from the geometry and real inequalities
in our local research draft, using the accepted OpenAI manuscript's notation.
It proves identities and inequalities of real numbers only. In particular,
the subset-loss theorem absorbs a specified algebraic loss formula; it does
not assert that an analytic row moment satisfies that formula.

There is no analytic nonvanishing theorem, imported OpenAI theorem, new axiom,
or unproved declaration in this module.
-/

namespace LW56e2.Transport.Geometry

noncomputable section

def ell (p : ℝ) : ℝ := 1 / 6 + p

def width (p : ℝ) : ℝ := 5 / 6 - p

def lx (p : ℝ) : ℝ := 17 / 48 - p / 2

def ly (p : ℝ) : ℝ := 23 / 48 - p / 2

def h (p : ℝ) : ℝ := 13 / 16 + 3 * p / 2

def b : ℝ := 1 / 8

def boundary (p : ℝ) : ℝ := 7 / 8 - p / 4

def signal (p s : ℝ) : ℝ := s + lx p / 2 - 1 + h p / 6

def lowExponent (p : ℝ) : ℝ := lx p / 2 + b / 12

def subsetWidth (p d : ℝ) : ℝ := width p - 2 * d

def subsetEll (p d : ℝ) : ℝ := ell p - d

def subsetLoss (p d : ℝ) : ℝ :=
  -d + max 0 (5 * ell p - 1 + d) / 8

theorem width_eq_sum (p : ℝ) : width p = lx p + ly p := by
  dsimp [width, lx, ly]
  ring

theorem width_add_ell (p : ℝ) : width p + ell p = 1 := by
  dsimp [width, ell]
  ring

theorem h_eq (p : ℝ) : h p = 1 - lx p + ell p := by
  dsimp [h, lx, ell]
  ring

theorem ly_eq (p : ℝ) : ly p = lx p + b := by
  dsimp [ly, lx, b]
  ring

theorem signal_eq (p s : ℝ) : signal p s = s - 11 / 16 := by
  dsimp [signal, lx, h]
  ring

theorem signal_difference (p s t : ℝ) :
    signal p s - signal p t = s - t := by
  rw [signal_eq, signal_eq]
  ring

theorem lowExponent_eq (p : ℝ) :
    lowExponent p = 3 / 16 - p / 4 := by
  dsimp [lowExponent, lx, b]
  ring

theorem lowExponent_eq_signal_boundary (p : ℝ) :
    lowExponent p = signal p (boundary p) := by
  rw [lowExponent_eq, signal_eq]
  dsimp [boundary]
  ring

theorem boundary_decrement (p : ℝ) :
    (7 / 8 : ℝ) - boundary p = p / 4 := by
  dsimp [boundary]
  ring

theorem boundary_lt_seven_eighths {p : ℝ} (hp : 0 < p) :
    boundary p < 7 / 8 := by
  dsimp [boundary]
  linarith

theorem boundary_gt_thirteen_fifteenths {p : ℝ}
    (hp : p < 1 / 30) : (13 / 15 : ℝ) < boundary p := by
  dsimp [boundary]
  linarith

theorem ell_pos {p : ℝ} (hp : 0 < p) : 0 < ell p := by
  dsimp [ell]
  linarith

theorem ell_lt_one_fifth {p : ℝ} (hp : p < 1 / 30) :
    ell p < 1 / 5 := by
  dsimp [ell]
  linarith

theorem h_pos {p : ℝ} (hp : 0 < p) : 0 < h p := by
  dsimp [h]
  linarith

theorem h_lt_one {p : ℝ} (hp : p < 1 / 30) : h p < 1 := by
  dsimp [h]
  linarith

theorem subset_width_identity (p d : ℝ) :
    subsetWidth p d + subsetEll p d - 1 = -3 * d := by
  dsimp [subsetWidth, subsetEll, width, ell]
  ring

theorem reflected_numerator_identity (p d : ℝ) :
    1 + 3 * subsetEll p d - 2 * subsetWidth p d =
      5 * ell p - 1 + d := by
  dsimp [subsetEll, subsetWidth, ell, width]
  ring

theorem min_subset_width (p : ℝ) :
    subsetWidth p (ell p) = 1 / 2 - 3 * p := by
  dsimp [subsetWidth, width, ell]
  ring

theorem subsetWidth_gt_two_fifths {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (2 / 5 : ℝ) < subsetWidth p d := by
  dsimp [subsetWidth, width]
  dsimp [ell] at hd
  linarith

theorem subsetEll_nonneg {p d : ℝ} (hd : d ≤ ell p) :
    0 ≤ subsetEll p d := by
  dsimp [subsetEll]
  linarith

theorem lx_residual_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (11 / 80 : ℝ) < lx p - d := by
  dsimp [lx]
  dsimp [ell] at hd
  linarith

theorem ly_residual_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (21 / 80 : ℝ) < ly p - d := by
  dsimp [ly]
  dsimp [ell] at hd
  linarith

theorem gram_margin_gt {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (1 / 30 : ℝ) < ly p - d - 11 * b / 6 := by
  dsimp [ly, b]
  dsimp [ell] at hd
  linarith

theorem supply_margin_identity (p : ℝ) :
    5 * ell p - h p = 1 / 48 + 7 * p / 2 := by
  dsimp [ell, h]
  ring

theorem supply_margin_pos {p : ℝ} (hp : 0 < p) :
    0 < 5 * ell p - h p := by
  rw [supply_margin_identity]
  linarith

theorem supply_gt_one_fifth {p : ℝ} (hp : 0 < p) :
    (1 / 5 : ℝ) < ell p / h p := by
  apply (lt_div_iff₀ (h_pos hp)).2
  have hm := supply_margin_pos hp
  linarith

theorem supply_gt_inverse_capacity {p : ℝ} (hp : 0 < p) :
    (7 / 37 : ℝ) < ell p / h p := by
  have hs := supply_gt_one_fifth hp
  linarith

/-- The positive-part term is bounded by the subset length. This uses only
the upper bound on p and nonnegativity of d; an upper bound on d
is unnecessary for this particular inequality. -/
theorem positive_part_le_subset {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    max 0 (5 * ell p - 1 + d) ≤ d := by
  have he := ell_lt_one_fifth hp
  apply max_le
  · exact hd
  · linarith

theorem subsetLoss_le_linear {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    subsetLoss p d ≤ -(7 / 8 : ℝ) * d := by
  have hm := positive_part_le_subset hp hd
  dsimp [subsetLoss]
  linarith

/-- Algebraic absorption on the actual subset-length interval. -/
theorem subsetLoss_nonpos {p d : ℝ}
    (_hp0 : 0 < p) (hp : p < 1 / 30)
    (hd0 : 0 ≤ d) (_hdell : d ≤ ell p) :
    subsetLoss p d ≤ 0 := by
  have hm := subsetLoss_le_linear hp hd0
  linarith

theorem subsetLoss_zero {p : ℝ} (hp : p < 1 / 30) :
    subsetLoss p 0 = 0 := by
  have he := ell_lt_one_fifth hp
  have hn : 5 * ell p - 1 + 0 ≤ 0 := by linarith
  dsimp [subsetLoss]
  rw [max_eq_left hn]
  ring

/-- At the fully rescaled subset, the specified row-energy loss before
Cauchy--Schwarz is 3p/2. This is only a formula evaluation. -/
theorem full_subset_row_loss {p : ℝ} (hp : 0 < p) :
    max 0 (5 * ell p - 1 + ell p) / 4 = 3 * p / 2 := by
  have hn : 0 ≤ 5 * ell p - 1 + ell p := by
    dsimp [ell]
    linarith
  rw [max_eq_right hn]
  dsimp [ell]
  ring

end

end LW56e2.Transport.Geometry
