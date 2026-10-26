import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelSplit
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelPosition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The numeric certificates of the first-level LOW child with the second step: the inequalities between the constants of
the two-level ledger that the proof of the bound of one final daughter uses. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization

/-- The numeric certificates of the bound of one final daughter of a first-level LOW child with the second step, for
the grid of mesh `1/G`, the width bound `Mcap` of the states, the support padding `εpad` of the units, the bound
`ωmax` of the frequency loss, the slack `ξR` and the margin `δR` of the reflection test, and the slacks `gridSlack` and
`ampSlack` of the total length and the amplifier of the parent of the second step. All are inequalities between
constants and affine functions of the cell `b`, which are certified at the two ends of the window of the cells. -/
structure TwoLevelCertificates (G : ℕ) (Mcap εpad ωmax ξR δR gridSlack ampSlack : ℝ) : Prop where
  /-- The grid is at least a millionth fine. -/
  grid : 1000000 ≤ G
  /-- The width slack `Mcap - 1` of a state is at most six amplifiers of the first cell, so a widened child has width
  at most one. -/
  width : Mcap - 1 ≤ 6 * firstAmp firstCellTop
  /-- The paddings are at most nine ten-millionths. -/
  small : 2 * ωmax + εpad ≤ 9 / 10000000
  /-- The slope mesh of the cells, the slope less one times the mesh, is at most a ten-millionth: with the paddings it
  is at most a millionth, the slack of the position of the second step. -/
  mesh : (twoLevelSlope - 1) * cellMesh ≤ 1 / 10000000
  /-- The margin of the reflection test covers the overshoot of the zero-extraction child of every cell and the
  paddings. -/
  reflect : ∀ b, firstCellTop ≤ b → b ≤ slotTop → childOvershoot b + ωmax + εpad ≤ δR
  /-- The margin and the slack of the reflection test are at most a hundredth of the least width of the second
  step. -/
  reflect_margin : δR + ξR ≤ 1 / 100 * (2 / 5)
  /-- The margin of the reflection test is at most `7/2500`, so the overshoot of a child over the old region, which is
  at most the margin, is at most `7/2500`. -/
  reflect_small : δR ≤ 7 / 2500
  /-- The room of the direct deletion at the least margin covers the LOW reserve and the slacks of the width, the
  padding and the frequency loss, at the rate of the direct deletion. -/
  room : lowReserveAt twoLevelPrice twoLevelIntercept firstJunction +
    directDeletionRate * ((Mcap - 1) + εpad + 2 * ωmax) ≤ directDeletionMargin
  /-- The mesh of the grid, times the slope of the second step, is at most the slack of the total length. -/
  length : secondSlope / G ≤ gridSlack
  /-- The amplifier ratio of the second step times the paddings, and times the mesh of the grid with the slot price, is
  at most the slack of the amplifier. -/
  amp : amplifierRatio slotPrice 1 secondJunction * (2 * ωmax + εpad) +
    amplifierRatio slotPrice 1 secondJunction * (1 + 6 * slotPrice) / G ≤ ampSlack

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
