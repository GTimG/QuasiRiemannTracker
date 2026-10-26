import Mathlib.Tactic
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Bracket
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.SlotPrice
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The small allowances of the proof, defined once, and the losses derived from them.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The unit of the allowances of the analytic argument that only have to be positive: the cell
mesh, the allowance of the large-root tail and the weight of the LOW reserve. -/
def allowanceUnit : ℝ := 1/100000000

/-- Weight `alpha` of the LOW reserve `alpha (1 - q0/κ)`. Any positive weight works; it is the
allowance unit. The slacks of the marked ledger are proportional to it (`geometryLossCap`). -/
def lowReserveWeight : ℝ := allowanceUnit

/-- Width of the cells of the slot sum in the HIGH reserve. -/
def cellMesh : ℝ := allowanceUnit

/-- Bottom of the slot window of Collet's affine moment: the smallest total slot width for which
the affine moment is proved. -/
def slotFloor : ℝ := 17/500

theorem slotFloor_pos : 0 < slotFloor := by norm_num [slotFloor]

/-- The upper edge of the first cell of the slot window. -/
def firstCellTop : ℝ := slotFloor + cellMesh

theorem cellMesh_pos : 0 < cellMesh := by
  unfold cellMesh allowanceUnit
  norm_num

/-- The allowance `tailEps` of the large-root tail gain `κ (6 ρ - 1 - tailEps)` of the marked count:
the allowance unit. -/
def tailSlack : ℝ := allowanceUnit

/-- The cap of the geometry loss unit in the marked schedule: the unit is at most the LOW reserve
`alpha (1 - q/κ)` over `128`, which on the split range is largest at its bottom `q = 1/2`
(`geometry_loss_below_marked_cap`). -/
def geometryLossCap : ℝ := lowReserveWeight*(1 - (1/2)/slotPrice)/128

/-- The cap of the frequency loss of the live slots: the frequency loss is at most `33 μ/128` for
the geometry loss unit `μ ≤ geometryLossCap` (`eventual_geometry_small_frequency`). -/
def frequencyLossCap : ℝ := 33*geometryLossCap/128

/-- Width of the bins of the marked count. Any positive width works; the tiny-slot loss
`62 geometryLossCap/(2048 w)` falls with it (`tinySlotLoss`) while the bin-width term `2 w s` of the
marked loss for slot sums up to `s` grows with it (`markedLossAt`). It is the width at which the two
are equal, where their sum is smallest, for slot sums up to the first cell top (the start of the
window-top iteration, which depends on the width), rounded up to eight digits. -/
bracket_up markedBinWidth (digits := 8) : Real.sqrt (62*geometryLossCap/(4096*firstCellTop))
  unfolding [geometryLossCap, lowReserveWeight, firstCellTop, slotFloor, cellMesh, allowanceUnit,
    slotPrice, betaBound]

/-- The rate of the marked count: the smallest one for which the selector buffer
`e ≤ geometryLossCap/294912` and the witness rates `markedRate/128` fit in half of it
(`marked_buffer_budget`). -/
def markedRate : ℝ := geometryLossCap/432

/-- The pad of the marked count's raw exponent: any positive number works; it is the marked rate. -/
def markedPad : ℝ := markedRate

/-- Analytic loss charged to the marked saving for slot sums up to `s`: the raw error budget of
the marked count at raw exponent up to `130` and geometry loss unit up to `geometryLossCap`
(`marked_raw_error_budget`). -/
def markedLossAt (s : ℝ) : ℝ :=
  130*markedRate + 2*markedBinWidth*s + 131*(159*markedRate) + markedPad +
    geometryLossCap/32 + geometryLossCap/8

/-- The total width of the tiny slots that the marked ledger discards: the smallest one for which
the slot-loss gate holds at every geometry loss unit up to `geometryLossCap`
(`marked_slot_loss_gate`). -/
def tinySlotLoss : ℝ := 62*geometryLossCap/(2048*markedBinWidth)

/-- The width given up to the two common allocations: any positive allowance works; it is the
geometry loss cap. -/
def commonAllocationLoss : ℝ := geometryLossCap

/-- The slot width that the marked ledger loses before it is priced or kept live. -/
def supplyLoss : ℝ := commonAllocationLoss + tinySlotLoss

theorem allowanceUnit_pos : 0 < allowanceUnit := by
  unfold allowanceUnit
  norm_num

theorem geometryLossCap_pos : 0 < geometryLossCap := by
  have h : 1/2/slotPrice < 1 := (div_lt_one slotPrice_pos).mpr (by linarith [slotPrice_mem.1])
  unfold geometryLossCap lowReserveWeight allowanceUnit
  nlinarith

theorem markedRate_pos : 0 < markedRate := by
  unfold markedRate
  linarith [geometryLossCap_pos]

theorem markedLossAt_pos {s : ℝ} (hs : 0 ≤ s) : 0 < markedLossAt s := by
  unfold markedLossAt markedPad markedBinWidth
  linarith [geometryLossCap_pos, markedRate_pos]

theorem commonAllocationLoss_pos : 0 < commonAllocationLoss := geometryLossCap_pos

theorem tinySlotLoss_pos : 0 < tinySlotLoss := by
  unfold tinySlotLoss markedBinWidth
  have := geometryLossCap_pos
  have := allowanceUnit_pos
  positivity

theorem supplyLoss_pos : 0 < supplyLoss := by
  unfold supplyLoss
  linarith [commonAllocationLoss_pos, tinySlotLoss_pos]

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
