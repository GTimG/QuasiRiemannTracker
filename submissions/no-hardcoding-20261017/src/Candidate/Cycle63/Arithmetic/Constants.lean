import Candidate.Cycle63.Optimization.Ledger
import Candidate.Cycle63.Arithmetic.Window
import Candidate.Cycle63.Certificate.Bracket

/-! The constants of the proof.

The claimed bound `theta` is the only presentation number. The parameters that the earlier trees fixed by
tuning are computed: Collet's bin split `q0` is the point where the price channel and the capped live
channel of the marked saving meet in the top cell, with the caps that the marked count provides
(`Cycle63.Optimization.markedSplit`, the root of the residual of the caps); the slope `lambda` is the one
for which the price bound of the HIGH reserve is the same in every cell, the intercept `B` is the
largest one that bound allows, and the row length `h` is the optimum `hStar` of the top-row
certificate. Their enclosures are computed by `bracket` when this file is elaborated, so no enclosure
number appears in the source. The savings of the row certificates and the offset of the extended
row are fixed fractions of the claim margin `theta - thetaMin lambda B`, and the junction row length
is the root of the small-plain-capacity gate; `d0` is the remaining tolerance of the analytic
argument. Downstream proofs use the enclosures and identities below, not numeric values. -/

namespace Cycle63.Arithmetic

noncomputable section
open Cycle63.Optimization

def theta : ℝ := 874835173/1000000000
def c : ℝ := 1 - theta
/-- Collet's LOW/HIGH bin split: where both channels of the marked saving are tight in the top cell. -/
def q0 : ℝ := markedSplit
/-- Slot-free density exponent at the bin split. -/
def rho0 : ℝ := density q0
/-- Amplifier ratio of the LOW ledger. -/
def Ka : ℝ := amplifierRatio q0
/-- Slope of Collet's affine moment: the price bound of the HIGH reserve is the same in every cell. -/
def lambda : ℝ := movingSlope q0
def alpha : ℝ := lowReserveWeight
/-- Intercept of Collet's affine moment: the largest one the price channel allows in every cell. -/
def B : ℝ := priceIntercept q0
/-- Row length: the optimum of the top-row certificate. -/
def h : ℝ := hStar lambda B
def ell : ℝ := 11/3 - 4*theta
def x : ℝ := 1 + ell - h
def y : ℝ := h - 2*ell
def kappaStar : ℝ := 2*theta - 1
/-- The junction row length: the smallest row length at which the affine slot capacity at zero shift
is at most `Physical.smallPlainCap` (`Physical.affineCapacity_interior`). -/
def dMinus : ℝ := 2*y/(lambda*Physical.smallPlainCap + 2 - B)
/-- The claim margin: the claim less the class bound of the top-row certificate. The savings of the
row certificates and the offset of the extended row are paid from it. -/
def claimMargin : ℝ := theta - thetaMin lambda B
/-- The saving of the top row: three times the claim margin. The top row's margin is the claim
margin times `(9 λ + 6 λ δ + 12 δ)/(3 λ)`, which exceeds `3` at every zero parameter `δ > 0`
(`Bernstein.top_margin_half`). -/
def topSaving : ℝ := 3*claimMargin
/-- The offset of the extended row `dPlus = h + dPlusOffset`: a quarter of the top saving. The
exponent of the extended row grows with slope below `2` (`Bernstein.newSlope_lt_two`), so the
extended row keeps half of the top saving. -/
def dPlusOffset : ℝ := topSaving/4
/-- The saving of the rows other than the top row: the top saving less what the extended row
loses. -/
def rowSaving : ℝ := topSaving - 2*dPlusOffset
def dPlus : ℝ := h + dPlusOffset
def d0 : ℝ := 1/200
/-- The proportion of the shift that the shift reserve keeps in the large-shift regime. -/
def reserveProportion : ℝ := 1/500
/-- The split between the affine-capacity regime and the shift-reserve regime of the numerator
shifts: the smallest shift at which the shift reserve keeps the proportion `reserveProportion` for
every shift base up to `2 y/dMinus - 1` (`Physical.large_shift_reserve`). -/
def t0 : ℝ :=
  ((2*y/dMinus - 1)*(1/(4*lambda) - 1/18) - (1 - B)/(4*lambda))/(7/18 - reserveProportion)

/-- An enclosure of the bin split precise enough for the chain of enclosures below. -/
bracket q0_enclosure (digits := 14) : q0 using [markedSplit_enclosure] unfolding [q0]

bracket q0_bounds (digits := 9) : q0 using [q0_enclosure] unfolding []

bracket lambda_enclosure (digits := 14) : lambda using [q0_enclosure]
  unfolding [lambda, movingSlope, Cycle63.Optimization.slope, weight, amplifierRatio, density,
    priceEndRate]

bracket B_enclosure (digits := 14) : B using [q0_enclosure]
  unfolding [B, priceIntercept, lowReserveAt, movingSlope, Cycle63.Optimization.slope, weight,
    amplifierRatio, density, priceEndRate, markedLoss, markedRate, markedPad, slotTop, cellMesh,
    lowReserveWeight, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

bracket deltaStar_enclosure (digits := 13) : deltaStar lambda B using [lambda_enclosure, B_enclosure]
  unfolding [deltaStar, rootA2, rootA1, rootA0, rootDisc, discrim]

bracket firstCellTop_bounds (digits := 12) : firstCellTop
  unfolding [firstCellTop, slotFloor, cellMesh, allowanceUnit]
bracket slotTop_bounds (digits := 12) : slotTop unfolding [slotTop]

/-- The class bound of the top-row certificate at the computed parameters. -/
bracket thetaClass_bounds (digits := 12) : thetaMin lambda B
  using [lambda_enclosure, deltaStar_enclosure] unfolding [thetaMin, boundAt]

bracket h_enclosure (digits := 12) : h using [lambda_enclosure, B_enclosure, deltaStar_enclosure]
  unfolding [h, hStar, cutoffDen, thetaMin, boundAt, rootDisc, discrim, rootA2, rootA1, rootA0]

bracket lambda_bounds (digits := 9) : lambda using [lambda_enclosure] unfolding []
bracket B_bounds (digits := 9) : B using [B_enclosure] unfolding []
bracket deltaStar_bounds (digits := 9) : deltaStar lambda B using [deltaStar_enclosure] unfolding []
bracket h_bounds (digits := 9) : h using [h_enclosure] unfolding []

/-- The claim exceeds the class bound. -/
theorem claimMargin_pos : 0 < claimMargin := by
  have hb := thetaClass_bounds.2
  unfold claimMargin theta
  linarith

bracket claimMargin_bounds (digits := 15) : claimMargin using [thetaClass_bounds]
  unfolding [claimMargin, theta]
bracket topSaving_bounds (digits := 15) : topSaving using [claimMargin_bounds] unfolding [topSaving]
bracket dPlusOffset_bounds (digits := 15) : dPlusOffset using [claimMargin_bounds]
  unfolding [dPlusOffset, topSaving]
bracket rowSaving_bounds (digits := 15) : rowSaving using [claimMargin_bounds]
  unfolding [rowSaving, dPlusOffset, topSaving]

theorem topSaving_pos : 0 < topSaving := by unfold topSaving; linarith [claimMargin_pos]
theorem dPlusOffset_pos : 0 < dPlusOffset := by unfold dPlusOffset; linarith [topSaving_pos]
theorem rowSaving_pos : 0 < rowSaving := by unfold rowSaving dPlusOffset; linarith [topSaving_pos]
theorem rowSaving_add : rowSaving + 2*dPlusOffset = topSaving := by unfold rowSaving; ring

bracket dMinus_bounds (digits := 9) : dMinus using [lambda_enclosure, B_enclosure, h_enclosure]
  unfolding [dMinus, y, ell, theta, Physical.smallPlainCap, CountAffine.windowBottom,
    CountAffine.plainTop]

/-- The regime split of the numerator shifts. -/
bracket t0_bounds (digits := 12) : t0 using [lambda_enclosure, B_enclosure, h_enclosure]
  unfolding [t0, reserveProportion, y, dMinus, ell, theta, Physical.smallPlainCap,
    CountAffine.windowBottom, CountAffine.plainTop]

def lowReserve : ℝ := alpha*(1 - 4*q0/3)

/-- The price per unit of removed or frozen slot width: the common-prime rate of the valuation
estimate, `q0 - max(4 rho0 - 1, (2 + 22 rho0)/21)`. -/
def markedPrice : ℝ := ledgerPrice q0

/-- The ledger minimum of the marked saving in the cell with upper edge `b` and the bin with zero
parameter `δ`: the supplied width removed at the price, or live at the live cap with the marked rate
of the bin. -/
def markedGrossAt (b δ : ℝ) : ℝ := min (markedPrice*suppliedAt b) (liveRate δ*liveCap)

/-- On the enclosure of the bin split `rho0 ≥ 23/62`, so the valuation rate is `4 rho0 - 1`. -/
theorem markedPrice_eq : markedPrice = q0 - (4*rho0 - 1) := by
  have hq := q0_bounds
  have hρ : 23/62 ≤ rho0 := by
    apply le_of_lt; unfold rho0 density; rat_pos [hq]
  unfold markedPrice ledgerPrice
  rw [max_eq_left (by unfold rho0 at hρ; linarith)]
  rfl

theorem theta_eq : theta = 1 - c := by norm_num [theta, c]
theorem ell_eq : ell = 11 / 3 - 4 * theta := rfl
theorem x_eq : x = 1 + ell - h := rfl
theorem y_eq : y = h - 2 * ell := rfl
theorem kappaStar_eq : kappaStar = 2 * theta - 1 := rfl
theorem dMinus_eq : dMinus = 2*y/(lambda*Physical.smallPlainCap + 2 - B) := rfl
theorem dPlus_eq : dPlus = h + dPlusOffset := rfl

theorem ell_pos : 0 < ell := by norm_num [ell, theta]
theorem sixth_lt_ell : 1 / 6 < ell := by norm_num [ell, theta]
theorem ell_lt_fifth : ell < 1 / 5 := by norm_num [ell, theta]
theorem ell_lt_x : ell < x := by
  have := h_bounds; unfold x; linarith
theorem x_lt_y : x < y := by
  have := h_bounds; unfold x y; norm_num [ell, theta]; linarith
theorem y_lt_two_x : y < 2 * x := by
  have := h_bounds; unfold x y; norm_num [ell, theta]; linarith
theorem y_le : y ≤ 19 / 40 := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith

theorem y_lt_half : y < 1 / 2 := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith
theorem half_lt_h : 1 / 2 < h := by
  have := h_bounds; linarith
theorem h_lt_two_y : h < 2 * y := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith
theorem four_ell_lt_h : 4 * ell < h := by
  have := h_bounds; norm_num [ell, theta]; linarith
theorem x_add_y : x + y = 1 - ell := by unfold x y; ring
theorem d0_pos : 0 < d0 := by norm_num [d0]
theorem half_lt_dMinus : 1 / 2 < dMinus := by linarith [dMinus_bounds.1]
theorem dMinus_lt_h : dMinus < h := by linarith [dMinus_bounds.2, h_bounds.1]
theorem h_lt_dPlus : h < dPlus := by unfold dPlus; linarith [dPlusOffset_pos]
theorem dPlus_lt_one : dPlus < 1 := by
  have := h_bounds; have := dPlusOffset_bounds; unfold dPlus; linarith
theorem kappaStar_mem : 7 / 10 ≤ kappaStar ∧ kappaStar ≤ 3 / 4 := by
  constructor <;> norm_num [kappaStar, theta]
theorem alpha_pos : 0 < alpha := by norm_num [alpha, lowReserveWeight]

/-- The LOW reserve is small enough for the analytic payments: half of it is below `1/100`. -/
theorem lowReserve_le : lowReserve ≤ 1/50 := by
  have hq := q0_bounds
  unfold lowReserve alpha lowReserveWeight
  linarith

theorem lambda_bounds' : 39/10 < lambda ∧ lambda < 401/100 :=
  ⟨by linarith [lambda_bounds.1], by linarith [lambda_bounds.2]⟩

theorem lambda_pos : 0 < lambda := by linarith [lambda_bounds'.1]

theorem q0_pos : 0 < q0 := by linarith [q0_bounds.1]

theorem q0_lt : q0 < 3/4 := by linarith [q0_bounds.2]

/-- The slope in closed form, `(430 q0^2 - 399 q0 + 135)/(q0 E(q0))` with
`E(q) = 24 q^2 - 34 q + 35`. -/
theorem lambda_closed : lambda = (430*q0^2 - 399*q0 + 135)/(q0*(24*q0^2 - 34*q0 + 35)) :=
  movingSlope_closed q0_pos q0_lt

/-- Rewrites the computed parameters as rational functions of the bin split, for `rat_pos`. -/
macro "unfold_parameters" : tactic => `(tactic|
  (simp only [Cycle63.Arithmetic.B, Cycle63.Optimization.priceIntercept,
    Cycle63.Optimization.lowReserveAt, Cycle63.Arithmetic.lambda_closed,
    Cycle63.Optimization.movingSlope, Cycle63.Optimization.slope, Cycle63.Optimization.weight,
    Cycle63.Optimization.priceEndRate, Cycle63.Arithmetic.Ka, Cycle63.Arithmetic.markedPrice_eq,
    Cycle63.Optimization.markedLoss, Cycle63.Optimization.markedRate, Cycle63.Optimization.markedPad, Cycle63.Arithmetic.rho0, Cycle63.Arithmetic.alpha,
    Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.cellMesh,
    Cycle63.Optimization.slotFloor, Cycle63.Optimization.supplyLoss,
    Cycle63.Optimization.commonAllocationLoss, Cycle63.Optimization.tinySlotLoss,
    Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.markedBinWidth, Cycle63.Optimization.allowanceUnit,
    Cycle63.Arithmetic.lowReserve,
    Cycle63.Optimization.suppliedAt, Cycle63.Optimization.slotTop,
    Cycle63.Optimization.amplifierRatio, Cycle63.Optimization.density,
    Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.firstCellTop]))

theorem B_pos : 0 < B := by linarith [B_bounds.1]

end

end Cycle63.Arithmetic
