/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Basic.Real.Basic

namespace Qrh.TwoSlot.AnchorZeroLoss.High

/-- A positive witness shift, chosen before the physical data. The default
preserves the frozen finite construction; local instances permit smaller costs. -/
class WitnessShift where
  value : ℝ
  pos : 0 < value
  le_fixed : value ≤ 1/1000000000000

@[reducible] noncomputable instance fixedWitnessShift : WitnessShift where
  value := 1/1000000000000
  pos := by norm_num
  le_fixed := le_rfl

end Qrh.TwoSlot.AnchorZeroLoss.High
