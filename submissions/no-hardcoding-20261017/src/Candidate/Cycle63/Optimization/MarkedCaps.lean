/- The caps of the marked count, its bin top, its root cutoff and the bin split, each defined by the
constraint it meets with equality. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.Plane
import Candidate.Cycle63.Optimization.Slacks
import Candidate.Cycle63.Certificate.Root

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-! The marked count is used in the bins `δ = 2a - 1` from the bin split `q` up to the bin top `d`.
There it is at least `1 - c_L δ` (`VariableSupply.count_lower`), and its inverse and plain moment
estimates select slots of total widths at most `w_I` and `w_P`. Larger caps raise the live gain of
the marked count, so each cap is the largest one its constraint allows:

* the inverse length cap is `c_L` and the plain length cap `c_L/2` (`VariableSupply.fiber_exponent`);
* the inverse moment needs `c_L + 2 w_I ≤ 1`, so `w_I = u/2` with the cap unit `u = 1 - c_L`;
* the plain moment needs `c_L + 6 κ_p w_P ≤ 1` for the plain capacity cost `κ_p`, so
  `w_P = u/(6 κ_p)`;
* the count bound at the bin top `d` for the chosen width `s = (2 w_I + w_P)/3 = k u`, with
  `k = (1 + 1/(6 κ_p))/3`, needs `(5 - 2d) c_L ≥ 10/3 + s (5 - 6d)`, so
  `u = (5/3 - 2d)/(5 - 2d + k (5 - 6d))` (`capUnitAt`).

The caps fall as the bin top rises, so the bin top is the smallest one for which the growth of the
HIGH reserve above the bin split pays the net marked saving (`priceEndBinTop`), and the root cutoff
`κ` is the smallest one for which the large-root tail dominates the live gain at the bin top
(`rootCutoffAt`).

The marked saving in the cell `b` of the slot sum (`b - cellMesh ≤ Σ w ≤ b`) is the smaller of the
price channel, the price times the supplied width `b - cellMesh - supplyLoss`, and the capped live
channel, the live rate times the live cap. The slope `movingSlope` makes the HIGH reserve plus the
price channel the same in every cell, so the intercept of the price channel is one number
(`priceIntercept`); the capped live channel binds only in the top cell. The bin split is the point
where both channels are tight in the top cell: the root of `capResidual`, the product of the inverse
width cap and the core factor that balances the capped live channel at `q`, less the one that the
count provides with the bin top of `q`. -/

/-- Capacity cost per unit of plain slot width in the plain moment: `2 β - 1 ≤ 3/4` for the zeros
of real part `β ≤ 7/8` of the baseline region. -/
def plainCapacityCost : ℝ := 3/4

/-- The chosen width `(2 w_I + w_P)/3` per unit of the cap unit `u`, for `w_I = u/2` and
`w_P = u/(6 κ_p)`. -/
def chosenPerUnit : ℝ := (1 + 1/(6*plainCapacityCost))/3

/-- The ratio of the chosen width to the inverse width at the caps. -/
def liveRatio : ℝ := 2*chosenPerUnit

/-- The saving per unit of live slot width at slot amplitude `1/2` in the bin with zero
parameter `d`. -/
def halfGain (d : ℝ) : ℝ := d*(5 - 6*d)/(5 - 2*d)

/-- The live rate of the marked count in the bin `d`: the half-amplitude gain per unit of the
inverse width at the caps. -/
def liveRate (d : ℝ) : ℝ := liveRatio*halfGain d

/-- The common-prime rate `q - (4 ρ - 1)` of the valuation estimate at the bin split `q` where
`ρ ≥ 23/62`, so that `4 ρ - 1` is the larger of its two rates (`ledgerPrice`). -/
def priceEndRate (q : ℝ) : ℝ := q - (4*density q - 1)

/-- The slope of the affine plain moment at the bin split `q` for which the price bound of the HIGH
reserve is the same in every cell: the cancellation slope lowered by the price over `q + W`. -/
def movingSlope (q : ℝ) : ℝ := slope q - priceEndRate q/(q + weight q)

/-- The slot width that the marked count credits in the cell with upper edge `b`: the cell's lower
edge less the width lost to the two common allocations and to the tiny-slot discard. -/
def suppliedAt (b : ℝ) : ℝ := b - cellMesh - supplyLoss

/-- The amplifier length of the cell `b` at the bin split `q` for the intercept `B`. -/
def cellAmplifier (q B b : ℝ) : ℝ :=
  amplifierRatio q*(B - 1 + (9/2 - movingSlope q)*b) + lowReserveWeight

/-- The HIGH reserve before savings at the bin split `q` in the cell `b`, for the intercept `B`. -/
def cellHigh (q B b : ℝ) : ℝ :=
  1 - density q - q*(B - (movingSlope q - 1)*(b - cellMesh)) - cellAmplifier q B b*(5 - 6*density q)

/-- The LOW reserve `alpha (1 - 4 q/3)` at the bin split `q`. -/
def lowReserveAt (q : ℝ) : ℝ := lowReserveWeight*(1 - 4*q/3)

/-- The intercept at which the HIGH reserve, credited with the supplied width at the price, keeps
the loss and the LOW reserve in every cell (with the moving slope this is one number). -/
def priceIntercept (q : ℝ) : ℝ :=
  (1 - density q + weight q - q*(movingSlope q - 1)*cellMesh - lowReserveWeight*(5 - 6*density q)
    - priceEndRate q*(cellMesh + supplyLoss) - markedLoss - lowReserveAt q)/(q + weight q)

/-- The growth rate of the HIGH reserve per unit of zero parameter above the bin split `q`, in the
top cell of the slot window, at the price intercept. -/
def priceEndGrowth (q : ℝ) : ℝ :=
  50*(1 - 6*cellAmplifier q (priceIntercept q) slotTop)/(3*(5 - 2*q)^2)
    - (priceIntercept q - (movingSlope q - 1)*(slotTop - cellMesh))

/-- The smallest bin top at which the growth of the HIGH reserve above the bin split `q` pays the
net saving of the price end in the top cell. -/
def priceEndBinTop (q : ℝ) : ℝ :=
  q + (priceEndRate q*suppliedAt slotTop - markedLoss)/priceEndGrowth q

/-- The cap unit `u = 1 - c_L` at the bin top `d`: the largest one for which the count bound holds
at `d` with the caps `w_I = u/2` and `w_P = u/(6 κ_p)`. -/
def capUnitAt (d : ℝ) : ℝ := (5/3 - 2*d)/(5 - 2*d + chosenPerUnit*(5 - 6*d))

/-- The smallest root cutoff at which the large-root tail `κ (6 ρ(d) - 1 - tailSlack)` dominates
the live gain at the inverse width cap `w` and the core factor `1 - 6 κ` in the bin `d`. -/
def rootCutoffAt (d w : ℝ) : ℝ :=
  liveRate d*w/((6*density d - 1 - tailSlack) + 6*liveRate d*w)

/-- The inverse width cap times the core factor at the bin top `d`. -/
def coreCapAt (d : ℝ) : ℝ := capUnitAt d/2*(1 - 6*rootCutoffAt d (capUnitAt d/2))

/-- The frequency factor `1 - 6 amp - ω` of the live slots at the top cell, at the price intercept
of the bin split `q`. -/
def frequencyFactorAt (q : ℝ) : ℝ :=
  1 - 6*cellAmplifier q (priceIntercept q) slotTop - frequencyLossCap

/-- The product of the inverse width cap and the core factor at which the capped live channel keeps
the loss and the LOW reserve in the top cell at the price intercept of the bin split `q`. -/
def balancedCoreCap (q : ℝ) : ℝ :=
  (lowReserveAt q + markedLoss - cellHigh q (priceIntercept q) slotTop)/
    (liveRate q*frequencyFactorAt q)

/-- The product of the inverse width cap and the core factor that balances the capped live channel
at the bin split `q`, less the one that the marked count provides with the bin top of `q`. -/
def capResidual (q : ℝ) : ℝ := balancedCoreCap q - coreCapAt (priceEndBinTop q)

/-- The bin split: the point of the split range at which the capped live channel and the price
channel of the marked saving meet in the top cell, with the caps that the count provides. -/
def markedSplit : ℝ := Certificate.firstNonneg capResidual (1/2) (37/50)

/-- The top of the range of bins in which the marked count is used. -/
def markedBinTop : ℝ := priceEndBinTop markedSplit

/-- The cap unit `1 - c_L` at the bin top. -/
def capUnit : ℝ := capUnitAt markedBinTop

/-- Width cap of the inverse slots. -/
def inverseWidthCap : ℝ := capUnit/2

/-- Width cap of the plain slots. -/
def plainWidthCap : ℝ := capUnit/(6*plainCapacityCost)

/-- The chosen width at the caps: the inverse cap counted twice and the plain cap once. -/
def chosenWidthCap : ℝ := (2*inverseWidthCap + plainWidthCap)/3

/-- Slope `c_L` of the lower bound `1 - c_L δ` of the marked count. -/
def countSlope : ℝ := 1 - capUnit

/-- Length cap of the inverse fibers. -/
def inverseLengthCap : ℝ := countSlope

/-- Length cap of the plain fibers. -/
def plainLengthCap : ℝ := countSlope/2

/-- The large-root cutoff of the marked count. -/
def markedRootCutoff : ℝ := rootCutoffAt markedBinTop inverseWidthCap

/-- The core factor `1 - 6 κ` of the live frequency, for the root cutoff `κ`. -/
def coreFactor : ℝ := 1 - 6*markedRootCutoff

/-- The largest amplifier length on the cell range: the one of the top cell. -/
def amplifierCap : ℝ := cellAmplifier markedSplit (priceIntercept markedSplit) slotTop

/-- The frequency factor of the live slots at the largest amplifier length. -/
def frequencyFactor : ℝ := 1 - 6*amplifierCap - frequencyLossCap

/-- The frequency of the live slots: the core factor times the frequency factor. -/
def liveFrequency : ℝ := coreFactor*frequencyFactor

/-- The live width cap: the inverse width cap at the live frequency. -/
def liveCap : ℝ := inverseWidthCap*liveFrequency

/-- The smallest growth rate of the HIGH reserve per unit of zero parameter above the bin split on
the cell range: the one of the top cell. -/
def reserveGrowth : ℝ := priceEndGrowth markedSplit

end

end Cycle63.Optimization
