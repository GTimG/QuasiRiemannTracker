import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.Channels
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.WindowTangency
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Argmin
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.SecondLevel
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The ledger of a first step whose LOW children are bounded by a second step. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The LOW children of the first step are deleted into the region of the second step at the second junction `q₁`
(`SecondLevel`) instead of the old region, so the channel ledger is taken at that region's slot price and intercept
and its class bound is a function of both junctions and of the window top. The class bound falls as the first
junction falls, until the rate channel of the HIGH reserve (`rateChannel`: the HIGH reserve plus the supplied slot
width removed at the common rate) no longer keeps the fee in the junction's bin and the lowest cell. So the first
junction is the crossing of that channel with the fee, and the second junction minimizes the class bound at the
first. They are found by alternation from the second junction `7/10`: twice at the lowest window top, then once at
the window top that the second pair gives. -/

/-- The margin of the second step's region. -/
def regionMargin : ℝ := allowanceUnit

/-- The class bound of the top-row certificate at the first junction `q`, the second junction `q₁` and the window
top `s`. -/
def twoLevelBound (q q₁ s : ℝ) : ℝ := classBoundIn (regionPrice q₁) (regionIntercept q₁ regionMargin) q s

/-- The rate channel of the first step's HIGH reserve in the bin of the first junction `q` and the lowest cell, less
the fee, at the second junction `q₁` and the window top `s`. -/
def twoLevelRateMargin (q q₁ s : ℝ) : ℝ :=
  rateChannel (regionPrice q₁) (regionIntercept q₁ regionMargin) q
      (planeSlope (regionPrice q₁) (regionIntercept q₁ regionMargin) q)
      (planeIntercept (regionPrice q₁) (regionIntercept q₁ regionMargin) q s) q firstCellTop -
    highFee (regionPrice q₁) (regionIntercept q₁ regionMargin) q s

bracket_crossing firstJunctionSeed :
    (fun q => twoLevelRateMargin q (7/10) firstCellTop) on (3/5) (17/25) unfolding *

bracket_argmin secondJunctionSeed :
    (fun q₁ => twoLevelBound firstJunctionSeed q₁ firstCellTop) on (17/25) (18/25) unfolding *

bracket_crossing firstJunctionFloor :
    (fun q => twoLevelRateMargin q secondJunctionSeed firstCellTop) on (3/5) (17/25) unfolding *

bracket_argmin secondJunctionFloor :
    (fun q₁ => twoLevelBound firstJunctionFloor q₁ firstCellTop) on (17/25) (18/25) unfolding *

bracket twoLevelSlope_enclosure (digits := 14) :
    planeSlope (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
      firstJunctionFloor unfolding *

bracket twoLevelIntercept_enclosure (digits := 14) :
    planeIntercept (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
      firstJunctionFloor firstCellTop unfolding *

bracket twoLevelDelta_enclosure (digits := 13) :
    deltaStar
      (planeSlope (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
        firstJunctionFloor)
      (planeIntercept (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
        firstJunctionFloor firstCellTop)
  using [twoLevelSlope_enclosure, twoLevelIntercept_enclosure] unfolding *

/-- The class bound of the two-level ledger at the lowest window top. -/
bracket twoLevelBound_enclosure (digits := 12) :
    twoLevelBound firstJunctionFloor secondJunctionFloor firstCellTop
  using [twoLevelSlope_enclosure, twoLevelDelta_enclosure] unfolding [twoLevelBound, classBoundIn, thetaMin, boundAt]

bracket twoLevelRow_enclosure (digits := 12) :
    hStar
      (planeSlope (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
        firstJunctionFloor)
      (planeIntercept (regionPrice secondJunctionFloor) (regionIntercept secondJunctionFloor regionMargin)
        firstJunctionFloor firstCellTop)
  using [twoLevelSlope_enclosure, twoLevelIntercept_enclosure, twoLevelDelta_enclosure]
  unfolding [hStar, cutoffDen, thetaMin, boundAt, rootDisc, discrim, rootA2, rootA1, rootA0]

/-- The balanced top of the capped top-row margin at the two-level plane of the junctions `q`, `q₁` for the window
top `s`. -/
def twoLevelTopAt (q q₁ s : ℝ) : ℝ :=
  balancedTop (planeSlope (regionPrice q₁) (regionIntercept q₁ regionMargin) q)
    (planeIntercept (regionPrice q₁) (regionIntercept q₁ regionMargin) q s) (twoLevelBound q q₁ s)
    (hStar (planeSlope (regionPrice q₁) (regionIntercept q₁ regionMargin) q)
      (planeIntercept (regionPrice q₁) (regionIntercept q₁ regionMargin) q s))

/-- The top of the slot window of the two-level ledger: the balanced top at the plane of the junctions for the
lowest window top, rounded up to the grid. -/
bracket_up slotTop (digits := 8) : twoLevelTopAt firstJunctionFloor secondJunctionFloor firstCellTop
  using [twoLevelSlope_enclosure, twoLevelIntercept_enclosure, twoLevelBound_enclosure, twoLevelRow_enclosure]
  unfolding [twoLevelTopAt, twoLevelBound, classBoundIn, balancedTop, tangentA, tangentB, tangentC, cappedQuadA,
    cappedQuadB, cappedQuadC, cappedLevelSlope, cappedLevelConst, ellAt]

/-- The second junction of the two-level ledger: the minimizer of the class bound at the window top and the first
junction of the lowest window top. -/
bracket_argmin secondJunction :
    (fun q₁ => twoLevelBound firstJunctionFloor q₁ slotTop) on (17/25) (18/25) unfolding *

/-- The first junction of the two-level ledger: the crossing of the rate channel with the fee at the second junction
and the window top. -/
bracket_crossing firstJunction :
    (fun q => twoLevelRateMargin q secondJunction slotTop) on (3/5) (17/25) unfolding *

bracket twoLevelLedgerSlope_enclosure (digits := 14) :
    planeSlope (regionPrice secondJunction) (regionIntercept secondJunction regionMargin) firstJunction unfolding *

bracket twoLevelLedgerIntercept_enclosure (digits := 14) :
    planeIntercept (regionPrice secondJunction) (regionIntercept secondJunction regionMargin) firstJunction
      slotTop unfolding *

bracket twoLevelLedgerDelta_enclosure (digits := 13) :
    deltaStar (planeSlope (regionPrice secondJunction) (regionIntercept secondJunction regionMargin) firstJunction)
      (planeIntercept (regionPrice secondJunction) (regionIntercept secondJunction regionMargin) firstJunction
        slotTop)
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure] unfolding *

/-- The class bound of the two-level ledger at its junctions and window top. -/
bracket twoLevelClassBound_enclosure (digits := 12) : twoLevelBound firstJunction secondJunction slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerDelta_enclosure]
  unfolding [twoLevelBound, classBoundIn, thetaMin, boundAt]

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
