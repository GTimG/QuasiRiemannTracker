import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.Plane
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.Slacks
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.ExactGain
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.LowRegion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The channels of the HIGH reserve with the balanced common rate and the exact marked gain, and the
plane they admit at a junction. The channel structure is that of tracker PR #63 (Zhongpai Gao,
`gao-balanced-marked-20261017`, `Target830/High/ChannelDefs.lean`); here the slope, the intercept and
the root cutoff are the solutions of the conditions they meet. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-! The marked count is used in the bins `δ = 2a - 1` from the junction `q` up to the bin top. In the
bin `d` it is at least `1 - c_L d` (`VariableSupply.count_lower`), and its inverse and plain moment
estimates select slots of total widths at most `w_I` and `w_P`. Larger caps raise the gain of the
marked count, so each cap is the largest one its constraint allows:

* the inverse length cap is `c_L` and the plain length cap `c_L/2` (`VariableSupply.fiber_exponent`);
* the inverse moment needs `c_L + 2 w_I ≤ 1`, so `w_I = u/2` with the cap unit `u = 1 - c_L`;
* the plain moment needs `c_L + 6 κ_p w_P ≤ 1` for the plain capacity cost `κ_p`, so
  `w_P = u/(6 κ_p)`;
* the count bound in the bin `d` for the chosen width `s = (2 w_I + w_P)/3 = k u`, with
  `k = (1 + 1/(6 κ_p))/3`, needs `(5 - 2d) c_L ≥ 10/3 + s (5 - 6d)`, so
  `u = (5/3 - 2d)/(5 - 2d + k (5 - 6d))` (`capUnitAt`).

In a bin `d` above the junction and a cell `b` of the slot sum, a marked label with removed width
`R`, live width `L` and live frequency `Q` saves at least the minimum of five channels on top of the
HIGH reserve `H` (`ExactGain.exact_gain_payment`): the common rate `γ` times the supplied width `S`
and the four affine forms of the exact gain `φ (2 min(L, u Q) + min(L, v Q))/3` at `L = S`, `Q = F`
(the half gain `φ`, the inverse cap `u` and the plain cap `v` of the bin, the live frequency `F` of
the cell). All channels are affine in the cell, so the two window ends suffice. The root cutoff `r`
is the smallest one at which the large-root tail `r (6ρ - 1 - tailSlack)` dominates the capped gain
in every bin (`dominantRoot`), so the count's saving is the exact gain itself.

At the junction the mixed form `φ (2S + vF)/3` meets the fee with equality, in every cell: the slope
`channelSlope` makes it independent of the cell and the intercept `channelIntercept` sets it to the
fee. -/

/-- Capacity cost per unit of plain slot width in the plain moment: `2 β - 1 ≤ 3/4` for the zeros
of real part `β ≤ 7/8` of the baseline region. -/
def plainCapacityCost : ℝ := 3/4

/-- The chosen width `(2 w_I + w_P)/3` per unit of the cap unit `u`, for `w_I = u/2` and
`w_P = u/(6 κ_p)`. -/
def chosenPerUnit : ℝ := (1 + 1/(6*plainCapacityCost))/3

/-- The saving per unit of live slot width at slot amplitude `1/2` in the bin with zero
parameter `d`. -/
def halfGain (d : ℝ) : ℝ := d*(5 - 6*d)/(5 - 2*d)

/-- The cap unit `u = 1 - c_L` in the bin `d`: the largest one for which the count bound holds at `d`
with the caps `w_I = u/2` and `w_P = u/(6 κ_p)`. -/
def capUnitAt (d : ℝ) : ℝ := (5/3 - 2*d)/(5 - 2*d + chosenPerUnit*(5 - 6*d))

/-- The slot width that the marked count credits in the cell with upper edge `b`: the cell's lower
edge less the width lost to the two common allocations and to the tiny-slot discard. -/
def suppliedAt (b : ℝ) : ℝ := b - cellMesh - supplyLoss

variable (price intercept : ℝ)

/-- The LOW reserve `alpha (1 - q I/κ)` at the junction `q`, for the LOW children deleted into the region of
slot price `κ` and intercept `I`. -/
def lowReserveAt (q : ℝ) : ℝ := lowReserveWeight*(1 - q*intercept/price)

/-- The balanced common rate of the bin `d`: the HIGH saving per unit of removed slot width
(`Physical.ValuationCone.commonRate`). -/
def commonRateAt (d : ℝ) : ℝ := d - max (3/19) (4*density d - 5/4)

/-- The inverse width cap of the marked count in the bin `d`. -/
def inverseCapAt (d : ℝ) : ℝ := capUnitAt d/2

/-- The plain width cap of the marked count in the bin `d`. -/
def plainCapAt (d : ℝ) : ℝ := capUnitAt d/(6*plainCapacityCost)

/-- The exact marked gain of the live width `S` at the live frequency `F` in the bin `d`, with the
inverse and plain caps of the bin. -/
def markedGain (d S F : ℝ) : ℝ := ExactGain.scaledGain (halfGain d) (inverseCapAt d) (plainCapAt d) S F

/-- The gain of the width `D S` at the frequency `D` is `D` times the gain of `S` at unit frequency. -/
theorem markedGain_scale (d S D : ℝ) (hD : 0 ≤ D) : markedGain d (D*S) D = D*markedGain d S 1 := by
  unfold markedGain ExactGain.scaledGain ExactGain.gain
  rw [mul_one, mul_one, mul_comm (inverseCapAt d) D, mul_comm (plainCapAt d) D,
    ← mul_min_of_nonneg _ _ hD, ← mul_min_of_nonneg _ _ hD]
  ring

/-- The amplifier length of the cell `b` for the plane with slope `lam` and intercept `B` at the
junction `q`. -/
def planeAmplifier (q lam B b : ℝ) : ℝ :=
  amplifierRatio price intercept q*(B - intercept + (6*price - lam)*b) + lowReserveWeight

/-- The HIGH reserve before savings in the bin `d` and the cell `b`. -/
def planeHigh (q lam B d b : ℝ) : ℝ :=
  1 - density d - d*(B - (lam - 1)*(b - cellMesh)) - planeAmplifier price intercept q lam B b*(5 - 6*density d)

/-- The live frequency of the cell `b` for the root cutoff `r`. -/
def planeFrequency (q lam B r b : ℝ) : ℝ :=
  (1 - 6*r)*(1 - 6*planeAmplifier price intercept q lam B b - frequencyLossCap)

/-- What the HIGH reserve keeps: the LOW reserve and the marked loss for slot sums up to `s`. -/
def highFee (q s : ℝ) : ℝ := lowReserveAt price intercept q + markedLossAt s

/-- The rate channel: all supplied width removed at the common rate. -/
def rateChannel (q lam B d b : ℝ) : ℝ := planeHigh price intercept q lam B d b + commonRateAt d*suppliedAt b

/-- The linear form of the exact gain: all supplied width live below both caps. -/
def linearChannel (q lam B d b : ℝ) : ℝ := planeHigh price intercept q lam B d b + halfGain d*suppliedAt b

/-- The mixed form of the exact gain: the supplied width live below the inverse cap, the plain cap
binding. -/
def mixedChannel (q lam B r d b : ℝ) : ℝ :=
  planeHigh price intercept q lam B d b +
      halfGain d*(2*suppliedAt b + plainCapAt d*planeFrequency price intercept q lam B r b)/3

/-- The fourth affine form of the exact gain: the inverse cap binding. -/
def inverseChannel (q lam B r d b : ℝ) : ℝ :=
  planeHigh price intercept q lam B d b +
      halfGain d*(2*inverseCapAt d*planeFrequency price intercept q lam B r b + suppliedAt b)/3

/-- The capped form of the exact gain: both caps binding. -/
def cappedChannel (q lam B r d b : ℝ) : ℝ :=
  planeHigh price intercept q lam B d b +
      halfGain d*(2*inverseCapAt d + plainCapAt d)*planeFrequency price intercept q lam B r b/3

/-- The coefficient of the capped exact gain in the bin `d`: the gain per unit of live frequency once
both caps bind. -/
def capCoefficient (d : ℝ) : ℝ := halfGain d*(2*inverseCapAt d + plainCapAt d)/3

/-- The smallest root cutoff at which the large-root tail `r (6ρ(d) - 1 - tailSlack)` per unit of
frequency dominates the capped gain `c (1 - 6r)` on the core frequency in the bin `d`. -/
def dominantRoot (d : ℝ) : ℝ :=
  capCoefficient d/((6*density d - 1 - tailSlack) + 6*capCoefficient d)

theorem halfGain_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 3/4) : 0 ≤ halfGain d := by
  unfold halfGain
  exact div_nonneg (mul_nonneg hd0 (by linarith)) (by linarith)

theorem capUnitAt_nonneg {d : ℝ} (hd : d ≤ 3/4) : 0 ≤ capUnitAt d := by
  unfold capUnitAt chosenPerUnit plainCapacityCost
  apply div_nonneg (by linarith)
  nlinarith

/-- In the bins up to `3/4` the gain grows with the frequency. -/
theorem markedGain_mono_frequency {d S F F' : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 3/4) (hF : F ≤ F') :
    markedGain d S F ≤ markedGain d S F' := by
  have hu := capUnitAt_nonneg hd
  exact ExactGain.scaledGain_mono_scale (halfGain_nonneg hd0 hd)
    (by unfold inverseCapAt; positivity) (by unfold plainCapAt plainCapacityCost; positivity) hF

/-- The gain is at most its capped form, the cap coefficient times the frequency. -/
theorem markedGain_le_capacity {d S F : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 3/4) :
    markedGain d S F ≤ capCoefficient d*F :=
  ExactGain.scaledGain_le_capacity _ _ _ _ _ (halfGain_nonneg hd0 hd)

theorem markedGain_zero {d : ℝ} (hd : d ≤ 3/4) : markedGain d 0 1 = 0 := by
  have hu := capUnitAt_nonneg hd
  exact ExactGain.gain_zero _ _ _ (by unfold inverseCapAt; positivity)
    (by unfold plainCapAt plainCapacityCost; positivity)

/-- The width less the gain at unit frequency grows with the width: the half gain is at most the zero
parameter. -/
theorem markedGain_deficit_mono {d x y : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 3/4) (hxy : x ≤ y) :
    d*x - markedGain d x 1 ≤ d*y - markedGain d y 1 := by
  have hle : halfGain d ≤ d := by
    unfold halfGain
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact ExactGain.deficit_mono (halfGain_nonneg hd0 hd) hle hxy

/-- The amplifier width per unit of LOW gap that the plain cap of the mixed channel adds. -/
def plainWeight (q r : ℝ) : ℝ := 2*amplifierRatio price intercept q*halfGain q*plainCapAt q*(1 - 6*r)

/-- The slope at which the mixed channel at the junction `q` is the same in every cell. -/
def channelSlope (q r : ℝ) : ℝ :=
  (q - 2*halfGain q/3 + 6*price*(weight price intercept q + plainWeight price intercept q r))/
    (q + weight price intercept q + plainWeight price intercept q r)

/-- The intercept at which the mixed channel at the junction keeps the fee, for the window top `s`. -/
def channelIntercept (q r s : ℝ) : ℝ :=
  (mixedChannel price intercept q (channelSlope price intercept q r) 0 r q s - highFee price intercept q s)/
    (q + weight price intercept q + plainWeight price intercept q r)

/-- The slope of the ledger's plane at the junction `q`, with the dominance root cutoff. -/
def planeSlope (q : ℝ) : ℝ := channelSlope price intercept q (dominantRoot q)

/-- The intercept of the ledger's plane at the junction `q` for the window top `s`, with the dominance
root cutoff. -/
def planeIntercept (q s : ℝ) : ℝ := channelIntercept price intercept q (dominantRoot q) s

/-- The class bound of the top-row certificate at the ledger's plane of the junction `q` for the window
top `s`. -/
def classBoundIn (q s : ℝ) : ℝ := thetaMin (planeSlope price intercept q) (planeIntercept price intercept q s)

/-- The cell slope of the mixed channel at the junction for the plane slope `lam`. -/
def mixedCellSlope (q lam r : ℝ) : ℝ :=
  q*(lam - 1) - (6*price - lam)*(weight price intercept q + plainWeight price intercept q r) + 2*halfGain q/3

/-- The mixed channel at the junction is affine in the cell. -/
theorem mixed_channel_cell (q lam B r b : ℝ) :
    mixedChannel price intercept q lam B r q b = mixedChannel price intercept q lam B r q 0 +
        b*mixedCellSlope price intercept q lam r := by
  unfold mixedChannel planeHigh planeFrequency planeAmplifier suppliedAt mixedCellSlope plainWeight weight
  ring

/-- The mixed channel at the junction is affine in the intercept, with slope `-(q + W + W')`. -/
theorem mixed_channel_intercept (q lam B r b : ℝ) :
    mixedChannel price intercept q lam B r q b = mixedChannel price intercept q lam 0 r q b -
        B*(q + weight price intercept q + plainWeight price intercept q r) := by
  unfold mixedChannel planeHigh planeFrequency planeAmplifier plainWeight weight
  ring

theorem mixedCellSlope_channelSlope {q r : ℝ}
    (hden : q + weight price intercept q + plainWeight price intercept q r ≠ 0) :
    mixedCellSlope price intercept q (channelSlope price intercept q r) r = 0 := by
  have h : channelSlope price intercept q r*(q + weight price intercept q + plainWeight price intercept q r) =
      q - 2*halfGain q/3 + 6*price*(weight price intercept q + plainWeight price intercept q r) :=
          div_mul_cancel₀ _ hden
  unfold mixedCellSlope
  linear_combination h

/-- At the channel slope the mixed channel at the junction does not depend on the cell. -/
theorem mixed_channel_cell_free {q r : ℝ} (hden : q + weight price intercept q + plainWeight price intercept q r ≠ 0)
    (B b b' : ℝ) :
    mixedChannel price intercept q (channelSlope price intercept q r) B r q b =
        mixedChannel price intercept q (channelSlope price intercept q r) B r q b' := by
  rw [mixed_channel_cell price intercept q (channelSlope price intercept q r) B r b,
    mixed_channel_cell price intercept q (channelSlope price intercept q r) B r b',
    mixedCellSlope_channelSlope price intercept hden]
  ring

/-- At the channel intercept the mixed channel at the junction keeps exactly the fee, in every cell. -/
theorem mixed_channel_fee {q r : ℝ} (hden : q + weight price intercept q + plainWeight price intercept q r ≠ 0)
    (s b : ℝ) :
    mixedChannel price intercept q (channelSlope price intercept q r) (channelIntercept price intercept q r s) r q b =
        highFee price intercept q s := by
  rw [mixed_channel_cell_free price intercept hden _ b s, mixed_channel_intercept]
  unfold channelIntercept
  rw [div_mul_cancel₀ _ hden]
  ring

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
