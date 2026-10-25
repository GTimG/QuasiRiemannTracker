/- Copyright (c) 2026 Sil. Apache-2.0.
Exact local ledger gates. These do not assert a moment estimate by themselves. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedLedger
noncomputable section

def lower (R P s d : ℝ) : ℝ :=
  (3 / 2) * (P + s + (7 / 3) * d - (5 / 6) * R)
def upper (R P s d : ℝ) : ℝ := (P - s - R / 2 - d) / 2

theorem reference_interval_width (R P s d : ℝ) :
    upper R P s d - lower R P s d = R - P - 2 * s - 4 * d := by
  dsimp [upper, lower]
  ring

theorem reference_interval_nonempty {R P s d : ℝ}
    (h : P + 2 * s + 4 * d < R) :
    ∃ l : ℝ, lower R P s d < l ∧ l < upper R P s d := by
  have hw := reference_interval_width R P s d
  refine ⟨(lower R P s d + upper R P s d) / 2, ?_, ?_⟩ <;> linarith

theorem reference_gate {R P s d l : ℝ}
    (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hcap : P + 2 * s + 4 * d < R)
    (hcenter : (5 / 6) * R - (7 / 3) * d < P + s)
    (hl : lower R P s d < l) (hu : l < upper R P s d) :
    0 < l ∧ l < P / 2 ∧ R + d + 2 * l - P + s < R / 2 ∧
    l + (R + d) / 2 + s < (4 / 5) * R := by
  dsimp [lower, upper] at hl hu
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem principal_common_saving {l v : ℝ} (_hl : 0 ≤ l) (_hv : 0 ≤ v) :
    (2 / 3) * l ≤ (2 / 3) * v + (7 / 10) * max (l - v) 0 := by
  by_cases h : l ≤ v
  · rw [max_eq_right (by linarith : l - v ≤ 0)]
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ l - v)]
    linarith

theorem slot_reserve (S : ℝ) :
    (43 / 100) * S - (3 / 4) * ((57 / 100) * S) = S / 400 := by
  ring

theorem slot_gate {S d s : ℝ} (hS : 0 < S)
    (hd : (43 / 100) * S ≤ d) (hs : s ≤ S - d) :
    (3 / 4) * s < d := by
  linarith

theorem second_diagonal_gate {R P s d : ℝ}
    (hs : 0 ≤ s) (hd : 0 ≤ d) (h : P + 2 * s + 4 * d < R) :
    P + s - R + 3 * d < 0 := by
  linarith

theorem exceptional_transport_cancellation (d : ℝ) :
    (-2 * d - 4 * d) / 6 - d + 2 * d = 0 := by
  ring

theorem feedback_coefficient :
    (1 / 8 : ℝ) - 5 / 288 - 25 / 784 = 1069 / 14112 := by
  norm_num

end
end Candidate.SilPrior.FourthPower.MixedLedger
