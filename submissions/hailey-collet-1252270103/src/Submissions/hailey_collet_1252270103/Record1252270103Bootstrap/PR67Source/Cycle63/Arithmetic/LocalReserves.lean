import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! The reserves of Collet's coupled plane on the cell range `b ∈ [firstCellTop, slotTop]`.

Every reserve is a formula of the computed parameters. A reserve that the cell variable enters
affinely is bounded below on the range by `cellMin`, its smaller value at the two cell edges, so no
sign of a slope is assumed. Numerical facts are proved over the enclosure of the bin split by the
kernel-evaluated Bernstein test `rat_pos`. -/

namespace Cycle63.Arithmetic

noncomputable section
open Cycle63.Optimization

def g (b : ℝ) : ℝ := B - 1 + (6 * slotPrice - lambda) * b
/-- The gap of the cell `b` over the region of the LOW children. -/
def regionGap (b : ℝ) : ℝ := B - lowRegionIntercept + (6 * lowRegionPrice - lambda) * b
def amp (b : ℝ) : ℝ := Ka * regionGap b + alpha
-- The lower edge is one mesh step below the cell's upper edge.
def totalA (b : ℝ) : ℝ := B - (lambda - 1) * (b - cellMesh)
/-- The upper edge of the cell `j` of the slot window. -/
def cellUpper (j : ℕ) : ℝ := slotFloor + (j : ℝ)*cellMesh

theorem cellUpper_bounds {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ cellCount) :
    firstCellTop ≤ cellUpper j ∧ cellUpper j ≤ slotTop := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hn : (j : ℝ) ≤ (cellCount : ℝ) := by exact_mod_cast hjn
  have hm := cellMesh_pos
  have hc := cellCount_mul
  unfold cellUpper firstCellTop
  constructor <;> nlinarith

/-- The smaller value of a function at the two edges of the cell range. -/
def cellMin (f : ℝ → ℝ) : ℝ := min (f firstCellTop) (f slotTop)

/-- On the cell range an affine function is at least its smaller edge value. -/
theorem cellMin_le (f : ℝ → ℝ) (hf : ∀ b, f b = f 0 + (f 1 - f 0) * b) {b : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) : cellMin f ≤ f b := by
  unfold cellMin
  have hlo := hf firstCellTop
  have hhi := hf slotTop
  have hmid := hf b
  rcases le_total 0 (f 1 - f 0) with h | h
  · refine (min_le_left _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hb.1 h]
  · refine (min_le_right _ _).trans ?_
    nlinarith [mul_le_mul_of_nonpos_left hb.2 h]

/-- Both edge values exceed `r`, hence so does `cellMin`. -/
theorem lt_cellMin {f : ℝ → ℝ} {r : ℝ} (h₁ : r < f firstCellTop) (h₂ : r < f slotTop) :
    r < cellMin f :=
  lt_min h₁ h₂

theorem cell_mem {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    b ∈ Set.Icc firstCellTop slotTop := hb

theorem g_pos {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) : 0 < g b := by
  have hq := q0_bounds
  have hc := cell_mem hb
  have hf := firstCellTop_bounds
  have ht := slotTop_bounds
  unfold g
  unfold_parameters
  rat_pos [hq, hc, hf, ht, lambda_enclosure, B_enclosure]

/-- The amplifier width of the top cell is the amplifier cap of the marked count. -/
theorem amp_top : amp slotTop = amplifierCap := rfl

/-- The amplifier width grows with the cell. -/
theorem amp_slope_nonneg : 0 ≤ Ka * (6 * lowRegionPrice - lambda) := by
  have hq := q0_bounds
  have hp := lowRegionPrice_bounds
  have hK : 0 ≤ Ka := by
    have hlt : q0 * lowRegionIntercept < lowRegionPrice :=
      (div_lt_one (by linarith [hp.1])).mp (lt_of_le_of_lt lowRegionRatio_bounds.2 (by norm_num))
    unfold Ka amplifierRatio
    exact div_nonneg (by linarith [hq.1]) (by linarith)
  exact mul_nonneg hK (by linarith [lambda_bounds.2, hp.1])

/-- The smallest amplifier width on the cell range: the one of the first cell. -/
def amplifierFloor : ℝ := amp firstCellTop

bracket amplifierFloor_bounds (digits := 9) : amplifierFloor
  using [q0_enclosure, lambda_enclosure, B_enclosure, firstCellTop_bounds]
  unfolding [amplifierFloor, amp, regionGap, Ka, amplifierRatio, lowRegionPrice, lowRegionIntercept, regionPrice,
    regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin, secondJunction, alpha,
    lowReserveWeight, allowanceUnit, slotPrice, betaBound]

theorem amplifierFloor_pos : 0 < amplifierFloor := by linarith [amplifierFloor_bounds.1]

/-- The constant of the prime payment of the main source: `56 (2/a + 12)` at the amplifier floor `a`
(`Physical.geometry_main_prime_payment`). -/
def primePaymentConstant : ℝ := 56*(2/amplifierFloor + 12)

theorem primePaymentConstant_ge : 56*(2/amplifierFloor + 12) ≤ primePaymentConstant := le_rfl

/-- Bounds of the amplifier width on the cell range: it grows with the cell, from the amplifier
floor at the first cell up to the amplifier cap at the top cell. -/
theorem amp_bounds {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    amplifierFloor ≤ amp b ∧ amp b ≤ amplifierCap := by
  have hslope := amp_slope_nonneg
  constructor
  · unfold amplifierFloor amp regionGap
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hslope]
  · rw [← amp_top]
    unfold amp regionGap
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hslope]

theorem amp_pos {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) : 0 < amp b :=
  amplifierFloor_pos.trans_le (amp_bounds hb).1

/-- The frequency factor `1 - 6 amp - ω` of the live slots in the cell `b`. -/
def frequencyAt (b : ℝ) : ℝ := 1 - 6*amp b - frequencyLossCap

/-- In every cell the frequency factor exceeds `4/5` by twice the supplied width. -/
theorem frequencyAt_lower {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    4/5 + 2*suppliedAt b ≤ frequencyAt b := by
  have ha := (amp_bounds hb).2
  have hc := amplifierCap_bounds
  have hl := supplyLoss_pos
  have hm := cellMesh_pos
  have hω : frequencyLossCap ≤ 1/1000 := by
    norm_num [frequencyLossCap, geometryLossCap, lowReserveWeight, allowanceUnit, slotPrice, betaBound]
  have ht := slotTop_bounds
  unfold frequencyAt suppliedAt
  linarith

/-- The fee of the channel ledger is the room `lowReserve` plus the marked loss. -/
theorem highFee_eq : highFee lowRegionPrice lowRegionIntercept firstJunction slotTop = lowReserve + markedLoss := by
  rfl

theorem lowReserve_pos : 0 < lowReserve := by
  have hr := lowRegionRatio_bounds
  unfold lowReserve lowReserveAt lowReserveWeight allowanceUnit
  nlinarith [hr.2]

/-- The fraction of the amplifier width that the norms of the first step's amplifier primes reach. -/
def firstPrimeFraction : ℝ := 99/100

/-- The first error branch's reserve `(f - 1/2) amp - g/6` on the cell range, for the prime fraction `f`. -/
def firstErrorReserve : ℝ := cellMin (fun b => (firstPrimeFraction - 1/2) * amp b - g b / 6)

/-- The sixth error branch's reserve `(5 f - 1/2) amp - g/6` on the cell range. -/
def sixthErrorReserve : ℝ := cellMin (fun b => (5 * firstPrimeFraction - 1/2) * amp b - g b / 6)

/-- The seventh error branch's reserve `(6 f - 1/2) amp - g/6` on the cell range. -/
def seventhErrorReserve : ℝ := cellMin (fun b => (6 * firstPrimeFraction - 1/2) * amp b - g b / 6)

/-- The second-zero reserve `1 - totalA - 5 amp` on the cell range. -/
def zeroReserve : ℝ := cellMin (fun b => 1 - totalA b - 5 * amp b)

/-- The main fixed-inducing reserve `1 - totalA - 4 amp` on the cell range. -/
def mainFixedReserve : ℝ := cellMin (fun b => 1 - totalA b - 4 * amp b)

theorem first_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    firstErrorReserve ≤ (firstPrimeFraction - 1/2) * amp b - g b / 6 :=
  cellMin_le (fun b => (firstPrimeFraction - 1/2) * amp b - g b / 6) (fun b => by unfold amp regionGap g; ring) hb

theorem sixth_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    sixthErrorReserve ≤ (5 * firstPrimeFraction - 1/2) * amp b - g b / 6 :=
  cellMin_le (fun b => (5 * firstPrimeFraction - 1/2) * amp b - g b / 6) (fun b => by unfold amp regionGap g; ring)
    hb

theorem seventh_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    seventhErrorReserve ≤ (6 * firstPrimeFraction - 1/2) * amp b - g b / 6 :=
  cellMin_le (fun b => (6 * firstPrimeFraction - 1/2) * amp b - g b / 6) (fun b => by unfold amp regionGap g; ring)
    hb

theorem second_zero_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    zeroReserve ≤ 1 - totalA b - 5 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 5 * amp b) (fun b => by unfold totalA amp regionGap; ring) hb

theorem main_fixed_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    mainFixedReserve ≤ 1 - totalA b - 4 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 4 * amp b) (fun b => by unfold totalA amp regionGap; ring) hb

theorem lowReserve_lt_errorReserves :
    lowReserve < firstErrorReserve ∧ lowReserve < sixthErrorReserve ∧
      lowReserve < seventhErrorReserve := by
  have hq := q0_bounds
  refine ⟨?_, ?_, ?_⟩ <;>
  · first
    | (unfold firstErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold firstPrimeFraction amp regionGap g; unfold_parameters
         rat_pos [hq, lambda_enclosure, B_enclosure]))
    | (unfold sixthErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold firstPrimeFraction amp regionGap g; unfold_parameters
         rat_pos [hq, lambda_enclosure, B_enclosure]))
    | (unfold seventhErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold firstPrimeFraction amp regionGap g; unfold_parameters
         rat_pos [hq, lambda_enclosure, B_enclosure]))

/-- The density at the bin split lies in `[1/4, 23/50]`, the density range of the valuation cone. -/
theorem rho0_bounds : 1/4 ≤ rho0 ∧ rho0 ≤ 23/50 := by
  have hq := q0_bounds
  unfold rho0 density
  constructor <;> (apply le_of_lt; rat_pos [hq])

theorem supply_lower : 4 / 21 < ell / dPlus := by
  have hh := h_bounds
  have hz := dPlusOffset_bounds
  have hd : 0 < dPlus := by unfold dPlus; linarith [hh.1, hz.1]
  rw [lt_div_iff₀ hd]
  unfold dPlus
  norm_num [ell, theta]
  linarith [hh.2, hz.2]

end

end Cycle63.Arithmetic

end Record1252270103Bootstrap.PR67
