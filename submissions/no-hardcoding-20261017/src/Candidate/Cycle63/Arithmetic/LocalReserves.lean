import Candidate.Cycle63.Arithmetic.Constants

/-! The reserves of Collet's coupled plane on the cell range `b ∈ [firstCellTop, slotTop]`.

Every reserve is a formula of the computed parameters. A reserve that the cell variable enters
affinely is bounded below on the range by `cellMin`, its smaller value at the two cell edges, so no
sign of a slope is assumed. Numerical facts are proved over the enclosure of the bin split by the
kernel-evaluated Bernstein test `rat_pos`. -/

namespace Cycle63.Arithmetic

noncomputable section
open Cycle63.Optimization

def g (b : ℝ) : ℝ := B - 1 + (9 / 2 - lambda) * b
def amp (b : ℝ) : ℝ := Ka * g b + alpha
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
  rat_pos [hq, hc, hf, ht]

/-- The amplifier width of the top cell is the amplifier cap of the marked count. -/
theorem amp_top : amp slotTop = amplifierCap := by
  unfold amp g amplifierCap cellAmplifier Ka lambda alpha B
  rfl

/-- The amplifier width grows with the cell. -/
theorem amp_slope_nonneg : 0 ≤ Ka * (9 / 2 - lambda) := by
  have hq := q0_bounds
  rw [lambda_closed]
  unfold Ka amplifierRatio
  apply le_of_lt; rat_pos [hq]

/-- The smallest amplifier width on the cell range: the one of the first cell. -/
def amplifierFloor : ℝ := amp firstCellTop

bracket amplifierFloor_bounds (digits := 9) : amplifierFloor
  using [q0_enclosure, lambda_enclosure, B_enclosure, firstCellTop_bounds]
  unfolding [amplifierFloor, amp, g, Ka, amplifierRatio, alpha, lowReserveWeight]

theorem amplifierFloor_pos : 0 < amplifierFloor := by linarith [amplifierFloor_bounds.1]

/-- Bounds of the amplifier width on the cell range: it grows with the cell, from the amplifier
floor at the first cell up to the amplifier cap at the top cell. -/
theorem amp_bounds {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    amplifierFloor ≤ amp b ∧ amp b ≤ amplifierCap := by
  have hslope := amp_slope_nonneg
  constructor
  · unfold amplifierFloor amp g
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hslope]
  · rw [← amp_top]
    unfold amp g
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hslope]

theorem amp_pos {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) : 0 < amp b :=
  amplifierFloor_pos.trans_le (amp_bounds hb).1

/-- The LOW reserve: the intercept and the cell variable cancel. -/
theorem low_reserve (b : ℝ) :
    amp b * (1 - 4 * q0 / 3) - (2 * q0 / 9) * g b = lowReserve := by
  have hq : 9 - 12 * q0 ≠ 0 := by linarith [q0_bounds.2]
  unfold amp lowReserve
  exact low_reserve_cancel hq (g b) alpha

theorem lowReserve_pos : 0 < lowReserve := by
  unfold lowReserve alpha lowReserveWeight
  nlinarith [q0_bounds.2]

/-- The HIGH reserve at the bin split in the cell `b` is the room `lowReserve` minus the net saving
of the supplied width at the price: the slope makes the price channel tight in every cell. -/
theorem high_reserve (b : ℝ) :
    1 - rho0 - q0 * totalA b - amp b * (5 - 6 * rho0) =
      lowReserve - (markedPrice * suppliedAt b - markedLoss) := by
  have hpos : 0 < q0 + weight q0 := by
    have hq := q0_bounds
    unfold weight amplifierRatio density
    rat_pos [hq]
  have h := price_tight q0 b hpos.ne'
  have hp : markedPrice = priceEndRate q0 := by rw [markedPrice_eq]; rfl
  rw [hp]
  unfold cellHigh cellAmplifier lowReserveAt at h
  unfold totalA amp g rho0 Ka lambda lowReserve alpha B
  linarith

/-- The first error branch's reserve `amp/4 - g/6` on the cell range. -/
def firstErrorReserve : ℝ := cellMin (fun b => amp b / 4 - g b / 6)

/-- The sixth error branch's reserve `13 amp/4 - g/6` on the cell range. -/
def sixthErrorReserve : ℝ := cellMin (fun b => 13 * amp b / 4 - g b / 6)

/-- The seventh error branch's reserve `4 amp - g/6` on the cell range. -/
def seventhErrorReserve : ℝ := cellMin (fun b => 4 * amp b - g b / 6)

/-- The second-zero reserve `1 - totalA - 5 amp` on the cell range. -/
def zeroReserve : ℝ := cellMin (fun b => 1 - totalA b - 5 * amp b)

/-- The main fixed-inducing reserve `1 - totalA - 4 amp` on the cell range. -/
def mainFixedReserve : ℝ := cellMin (fun b => 1 - totalA b - 4 * amp b)

/-- The error fixed-inducing reserve `1 - totalA - 9 amp` on the cell range. -/
def errorFixedReserve : ℝ := cellMin (fun b => 1 - totalA b - 9 * amp b)

theorem first_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    firstErrorReserve ≤ amp b / 4 - g b / 6 :=
  cellMin_le (fun b => amp b / 4 - g b / 6) (fun b => by unfold amp g; ring) hb

theorem sixth_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    sixthErrorReserve ≤ 13 * amp b / 4 - g b / 6 :=
  cellMin_le (fun b => 13 * amp b / 4 - g b / 6) (fun b => by unfold amp g; ring) hb

theorem seventh_error_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    seventhErrorReserve ≤ 4 * amp b - g b / 6 :=
  cellMin_le (fun b => 4 * amp b - g b / 6) (fun b => by unfold amp g; ring) hb

theorem second_zero_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    zeroReserve ≤ 1 - totalA b - 5 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 5 * amp b) (fun b => by unfold totalA amp g; ring) hb

theorem main_fixed_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    mainFixedReserve ≤ 1 - totalA b - 4 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 4 * amp b) (fun b => by unfold totalA amp g; ring) hb

theorem error_fixed_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    errorFixedReserve ≤ 1 - totalA b - 9 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 9 * amp b) (fun b => by unfold totalA amp g; ring) hb

theorem lowReserve_lt_errorReserves :
    lowReserve < firstErrorReserve ∧ lowReserve < sixthErrorReserve ∧
      lowReserve < seventhErrorReserve := by
  have hq := q0_bounds
  refine ⟨?_, ?_, ?_⟩ <;>
  · first
    | (unfold firstErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold amp g; unfold_parameters; rat_pos [hq]))
    | (unfold sixthErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold amp g; unfold_parameters; rat_pos [hq]))
    | (unfold seventhErrorReserve; apply lt_cellMin <;>
        (rw [← sub_pos]; unfold amp g; unfold_parameters; rat_pos [hq]))

/-- The growth rate of the HIGH reserve in the zero bin is at least its value `reserveGrowth` at
the top cell, on the cell range: it falls with the cell. -/
theorem high_derivative_reserve {b : ℝ} (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) :
    reserveGrowth ≤ 50 * (1 - 6 * amp b) / (3 * (5 - 2 * q0) ^ 2) - totalA b := by
  have hq := q0_bounds
  have hq5 : (0:ℝ) < (5 - 2 * q0) ^ 2 := by nlinarith [hq.2]
  have hfall : 0 ≤ 100 * (Ka * (9 / 2 - lambda)) / (5 - 2 * q0) ^ 2 - (lambda - 1) := by
    rw [lambda_closed]
    unfold Ka amplifierRatio
    apply le_of_lt; rat_pos [hq]
  have hgrowth : reserveGrowth =
      50 * (1 - 6 * amp slotTop) / (3 * (5 - 2 * q0) ^ 2) - totalA slotTop := by
    unfold reserveGrowth priceEndGrowth cellAmplifier amp g totalA Ka lambda alpha B
    rfl
  have h5 : (5:ℝ) - 2 * q0 ≠ 0 := by linarith [hq.2]
  have hid : 50 * (1 - 6 * amp b) / (3 * (5 - 2 * q0) ^ 2) - totalA b - reserveGrowth =
      (slotTop - b) * (100 * (Ka * (9 / 2 - lambda)) / (5 - 2 * q0) ^ 2 - (lambda - 1)) := by
    rw [hgrowth]
    unfold amp g totalA
    field_simp
    ring
  have hb' : 0 ≤ slotTop - b := by linarith [hb.2]
  nlinarith [mul_nonneg hb' hfall]

/-- The density at the bin split lies in `[1/4, 2/5]`. -/
theorem rho0_bounds : 1/4 ≤ rho0 ∧ rho0 ≤ 2/5 := by
  have hq := q0_bounds
  unfold rho0 density
  constructor <;> (apply le_of_lt; rat_pos [hq])

/-- The price does not exceed the bin split. -/
theorem markedPrice_le_q0 : markedPrice ≤ q0 := by
  rw [markedPrice_eq]
  linarith [rho0_bounds.1]

/-- The price is positive. -/
theorem markedPrice_pos : 0 < markedPrice := by
  have hq := q0_bounds
  rw [markedPrice_eq]
  unfold rho0 density
  rat_pos [hq]

/-- The price exceeds twice the capped live rate of every bin of the HIGH range, as the marked
ledger requires. -/
theorem markedPrice_rate {δ : ℝ} (hδ : q0 ≤ δ ∧ δ ≤ 3/4) :
    2*liveRate δ*inverseWidthCap ≤ markedPrice := by
  have hq := q0_bounds
  have hw := inverseWidthCap_bounds
  rw [markedPrice_eq]
  unfold rho0 density liveRate liveRatio chosenPerUnit plainCapacityCost halfGain
  apply le_of_lt
  rat_pos [hq, hδ, hw]

/-- The live end of the ledger falls more slowly than the HIGH reserve grows, per unit of zero
parameter above the bin split. -/
theorem liveRate_drop {δ : ℝ} (hδ : q0 ≤ δ ∧ δ ≤ 3/4) :
    liveRate q0*liveCap - liveRate δ*liveCap ≤ (δ - q0)*reserveGrowth := by
  have hq := q0_bounds
  have hc := liveCap_bounds
  have hg := reserveGrowth_bounds
  have h1 : (5:ℝ) - 2*q0 ≠ 0 := by linarith [hq.2]
  have h2 : (5:ℝ) - 2*δ ≠ 0 := by linarith [hδ.2]
  have h1' := h1; ring_nf at h1'
  have h2' := h2; ring_nf at h2'
  have hid : liveRate q0*liveCap - liveRate δ*liveCap =
      (δ - q0)*(liveRatio*liveCap*(30*(q0 + δ) - 25 - 12*q0*δ)/((5 - 2*q0)*(5 - 2*δ))) := by
    unfold liveRate halfGain
    field_simp
    ring
  rw [hid]
  have hk : liveRatio*liveCap*(30*(q0 + δ) - 25 - 12*q0*δ)/((5 - 2*q0)*(5 - 2*δ)) ≤
      reserveGrowth := by
    unfold liveRatio chosenPerUnit plainCapacityCost
    apply le_of_lt; rat_pos [hq, hδ, hc, hg]
  nlinarith [mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hδ.1)]

/-- In every cell the gross marked saving falls more slowly than the HIGH reserve grows, per unit of
zero parameter above the bin split. -/
theorem markedGross_drop {b δ : ℝ} (hδ : q0 ≤ δ ∧ δ ≤ 3/4) :
    markedGrossAt b q0 - markedGrossAt b δ ≤ (δ - q0)*reserveGrowth := by
  have hr := liveRate_drop hδ
  have hnn : 0 ≤ (δ - q0)*reserveGrowth :=
    mul_nonneg (by linarith [hδ.1]) (by linarith [reserveGrowth_bounds.1])
  unfold markedGrossAt
  rcases le_total (markedPrice*suppliedAt b) (liveRate δ*liveCap) with h | h
  · rw [min_eq_left h (b := liveRate δ*liveCap)]
    linarith [min_le_left (markedPrice*suppliedAt b) (liveRate q0*liveCap)]
  · rw [min_eq_right h (a := markedPrice*suppliedAt b)]
    linarith [min_le_right (markedPrice*suppliedAt b) (liveRate q0*liveCap)]

/-- In every cell up to the top cell the gross marked saving at the bin split is the supplied width
at the price: the price channel and the capped live channel meet in the top cell. -/
theorem markedGross_split {b : ℝ} (hb : b ≤ slotTop) :
    markedGrossAt b q0 = markedPrice*suppliedAt b := by
  have hp : markedPrice = priceEndRate q0 := by rw [markedPrice_eq]; rfl
  have hmeet := price_eq_live_top
  have hpos : 0 ≤ markedPrice := markedPrice_pos.le
  have hs : suppliedAt b ≤ suppliedAt slotTop := by unfold suppliedAt; linarith
  have hle : markedPrice*suppliedAt b ≤ liveRate q0*liveCap := by
    rw [hp] at hpos ⊢
    calc priceEndRate q0*suppliedAt b ≤ priceEndRate q0*suppliedAt slotTop :=
          mul_le_mul_of_nonneg_left hs hpos
      _ = liveRate q0*liveCap := hmeet
  unfold markedGrossAt
  exact min_eq_left hle

theorem supply_lower : 4 / 21 < ell / dPlus := by
  have hh := h_bounds
  have hz := dPlusOffset_bounds
  have hd : 0 < dPlus := by unfold dPlus; linarith [hh.1, hz.1]
  rw [lt_div_iff₀ hd]
  unfold dPlus
  norm_num [ell, theta]
  linarith [hh.2, hz.2]

theorem principal_y_reserve : 0 < y / 20 - (1 + h) / 1000 - 1 / 4000 := by
  have hh := h_bounds
  unfold y
  norm_num [ell, theta]
  linarith [hh.1]

theorem principal_h_reserve : 0 < h / 600 - 1 / 1000 - 1 / 4000 := by
  have hh := h_bounds
  linarith [hh.1]

end

end Cycle63.Arithmetic
