/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIAsymmetricGeometry.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI.SevenEighths.AsymmetricGeometry

noncomputable section

abbrev skew : ℝ := 12457523527 / 15625000000000
abbrev lengthShift : ℝ := 42930200831 / 250000000000000
abbrev boundaryReduction : ℝ := 214651 / 5000000000
abbrev boundary : ℝ := 4374785349 / 5000000000
abbrev xBase : ℝ := 17 / 48 + skew
abbrev yBase : ℝ := 23 / 48 - skew
abbrev rowBase : ℝ := 13 / 16 - skew
abbrev lowBase : ℝ := 3 / 16 + skew / 3
abbrev signalOffset : ℝ := -11 / 16 + skew / 3
abbrev ratioExponent : ℝ := 1 / 8 - 2 * skew
abbrev compensatedCap : ℝ := 11 / 48 + 3 * skew
abbrev highMargin : ℝ := 1 / 1250000000000
abbrev lowAllowance : ℝ := 1 / 10000000000000
abbrev smallBudgetCap : ℝ := 1 / 10000000000000000

theorem verify_boundary : boundary = 7 / 8 - boundaryReduction := by
  norm_num

theorem bound_skew : 0 ≤ skew ∧ skew ≤ 1 / 1000 := by
  norm_num

theorem bound_length_shift : 0 < lengthShift ∧ lengthShift < 1 / 1000 := by
  norm_num

theorem verify_geometry (t : ℝ) :
    (xBase - t / 2) + (yBase - t / 2) + (1 / 6 + t) = 1 ∧
    (yBase - t / 2) - (xBase - t / 2) = ratioExponent ∧
    rowBase + 3 * t / 2 = 1 - (xBase - t / 2) + (1 / 6 + t) := by
  constructor
  · norm_num
    ring
  constructor <;> norm_num <;> ring

theorem verify_signal_exponent (s t : ℝ) :
    (xBase - t / 2) / 2 + s - 1 + (rowBase + 3 * t / 2) / 6 =
      s + signalOffset := by
  norm_num
  ring

theorem verify_low_margin :
    (boundary + signalOffset) - (lowBase - lengthShift / 4) =
      831 / 1000000000000000 := by
  norm_num

theorem bound_low_allowance :
    lowBase - lengthShift / 4 + lowAllowance < boundary + signalOffset := by
  norm_num

end

end OAI.SevenEighths.AsymmetricGeometry
