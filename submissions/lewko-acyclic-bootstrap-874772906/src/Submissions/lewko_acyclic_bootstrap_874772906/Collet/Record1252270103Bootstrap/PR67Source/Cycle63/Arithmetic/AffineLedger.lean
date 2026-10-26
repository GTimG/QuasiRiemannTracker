import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.Channels
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The ledger of a step of Collet's affine moment: the data of its plane, its slot window and the region
of its LOW children, the facts that the proofs of the step use, and the quantities derived from them.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The gap of the cell `b` over the region of slot price `price` and intercept `intercept`, for the plane of
slope `lam` and intercept `B`. -/
def planeGap (price intercept lam B b : ℝ) : ℝ := B - intercept + (6*price - lam)*b

/-- The bound of the total plain and slot length in the cell `b` of the plane of slope `lam` and intercept
`B`, for cells of width `mesh`. -/
def planeTotalLength (lam B mesh b : ℝ) : ℝ := B - (lam - 1)*(b - mesh)

/-- The cell `b` is the upper edge of the first cell of the slot window or its top. -/
abbrev OnCellEdge (slotFloor mesh slotTop b : ℝ) : Prop := b = slotFloor + mesh ∨ b = slotTop

/-- The plain lengths `n₁` and `n₂` and the slot sum `z` lie in the window of the plane of slope `lam` and
intercept `B`: each plain length is at least `windowBottom`, their sum is at least `sumBottom`, the slot sum lies
in `[slotFloor, slotTop]`, and the plane holds. -/
structure PlainWindow (windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z : ℝ) : Prop where
  left_ge : windowBottom ≤ n₁
  right_ge : windowBottom ≤ n₂
  sum_ge : sumBottom ≤ n₁ + n₂
  slots_ge : slotFloor ≤ z
  slots_le : z ≤ slotTop
  plane : n₁ + n₂ + lam * z ≤ B

theorem lowReserveWeight_pos : 0 < lowReserveWeight := allowanceUnit_pos

end

end Cycle63.Optimization

namespace Cycle63

/-- The ledger of a step of Collet's affine moment. Its data are the junction `q` of the LOW and HIGH bins,
the slope `lam` and the intercept `B` of the plane `n₁ + n₂ + lam z ≤ B M`, the slot price `price` and the
intercept `intercept` of the region into which the LOW children are deleted, the slot window
`[slotFloor, slotTop]` cut into `cellCount` cells of width `cellMesh`, the bottom `windowBottom` of each plain
length and `sumBottom` of their sum in units of `M`, the length `comparisonLength` of the first plain factor of
the comparison and the shortfall `plainLossCap` of the plain scales below `1/4`, the saving `zeroSaving` of the
second zero, and the fraction `primeFraction` of the amplifier width that the norm of an amplifier prime has at
least in the exponent. Its facts are the inequalities between them that the proofs of the step use. -/
class AffineLedger where
  /-- The junction of the LOW and HIGH bins. -/
  q : ℝ
  /-- The slope of the plane. -/
  lam : ℝ
  /-- The intercept of the plane. -/
  B : ℝ
  /-- The slot price of the region into which the LOW children are deleted. -/
  price : ℝ
  /-- The intercept of that region. -/
  intercept : ℝ
  /-- The bottom of the slot window. -/
  slotFloor : ℝ
  /-- The top of the slot window. -/
  slotTop : ℝ
  /-- The width of the cells of the slot window. -/
  cellMesh : ℝ
  /-- The number of cells of the slot window. -/
  cellCount : ℕ
  /-- The bottom of each plain length, in units of the width. -/
  windowBottom : ℝ
  /-- The bottom of the sum of the two plain lengths, in units of the width. -/
  sumBottom : ℝ
  /-- The length of the first plain factor of the comparison, in units of the width, as a function of the two
  plain lengths and the slot sum. -/
  comparisonLength : ℝ → ℝ → ℝ → ℝ
  /-- The largest shortfall below `1/4` of a plain length or of the first plain factor of the comparison. -/
  plainLossCap : ℝ
  /-- The saving of the second zero, in units of the width. -/
  zeroSaving : ℝ
  /-- The norm of an amplifier prime of width `a` is at least `Z ^ (primeFraction * a)`. -/
  primeFraction : ℝ
  /-- The junction is positive. -/
  q_pos : 0 < q
  /-- The junction is at least `1/50`, so the midpoint `(1 + q)/2` of the junction and one is at least `51/100`. -/
  one_fiftieth_le_q : 1 / 50 ≤ q
  /-- The slot price of the region is positive. -/
  price_pos : 0 < price
  /-- The slot price of the region is at most one. -/
  price_le_one : price ≤ 1
  /-- The junction is at most the slot price of the region. -/
  q_le_price : q ≤ price
  /-- The junction times the intercept is below the slot price of the region. -/
  q_intercept_lt_price : q * intercept < price
  /-- The slope of the plane is at least one. -/
  one_le_lam : 1 ≤ lam
  /-- The gap over the region does not decrease with the cell. -/
  lam_le_six_price : lam ≤ 6 * price
  /-- The gap over the old region does not decrease with the cell. -/
  lam_le_six_slotPrice : lam ≤ 6 * Optimization.slotPrice
  /-- The cells have a positive width. -/
  cellMesh_pos : 0 < cellMesh
  /-- The slot window has a cell. -/
  one_le_cellCount : 1 ≤ cellCount
  /-- The cells tile the slot window. -/
  cellCount_mul : (cellCount : ℝ) * cellMesh = slotTop - slotFloor
  /-- The top of the slot window is at most one. -/
  slotTop_le_one : slotTop ≤ 1
  /-- The bottom of the plain lengths is positive. -/
  windowBottom_pos : 0 < windowBottom
  /-- The intercept of the plane is at most one. -/
  B_le_one : B ≤ 1
  /-- The shortfall of the plain scales below `1/4` is not negative. -/
  plainLossCap_nonneg : 0 ≤ plainLossCap
  /-- The first plain factor of the comparison is not shorter than zero. -/
  comparisonLength_nonneg : ∀ n₁ n₂ z : ℝ,
    Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z →
      0 ≤ comparisonLength n₁ n₂ z
  /-- The first plain factor of the comparison is at most a quarter of the width. -/
  comparisonLength_le : ∀ n₁ n₂ z : ℝ,
    Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z →
      comparisonLength n₁ n₂ z ≤ 1 / 4
  /-- The second plain factor of the comparison is at least half the width. -/
  long_factor : ∀ n₁ n₂ z : ℝ,
    Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z →
      1 / 2 ≤ n₁ + n₂ - comparisonLength n₁ n₂ z
  /-- The reflected daughter of the comparison fits in the old region with a margin of `1/100` of the width. -/
  daughter_fits : ∀ n₁ n₂ z : ℝ,
    Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z →
      1 / 100 + 2 * comparisonLength n₁ n₂ z + (9 / 2) * z ≤ n₁ + n₂
  /-- The plain lengths and the first plain factor of the comparison fall short of `1/4` by at most
  `plainLossCap`. -/
  plainLoss_le : ∀ n₁ n₂ z : ℝ,
    Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z →
      1 / 4 - n₁ ≤ plainLossCap ∧ 1 / 4 - n₂ ≤ plainLossCap ∧ 1 / 4 - comparisonLength n₁ n₂ z ≤ plainLossCap
  /-- The saving of the second zero is positive. -/
  zeroSaving_pos : 0 < zeroSaving
  /-- The norm of an amplifier prime has an exponent above half the amplifier width. -/
  half_lt_primeFraction : 1 / 2 < primeFraction
  /-- The norm of an amplifier prime has an exponent below the amplifier width. -/
  primeFraction_lt_one : primeFraction < 1
  /-- The gap over the old region is positive in the first cell. -/
  oldGap_first_pos :
    0 < Optimization.planeGap Optimization.slotPrice 1 lam B (slotFloor + cellMesh)
  /-- The amplifier width is positive in the first cell. -/
  amp_first_pos : 0 < Optimization.planeAmplifier price intercept q lam B (slotFloor + cellMesh)
  /-- The amplifier width is at most one in the top cell. -/
  amp_top_le_one : Optimization.planeAmplifier price intercept q lam B slotTop ≤ 1
  /-- The LOW reserve is at most `1/50`. -/
  lowReserveAt_le : Optimization.lowReserveAt price intercept q ≤ 1 / 50
  /-- At the edges of the cell range the LOW reserve is at most the reserves of the first, sixth and seventh
  error branches. -/
  errorReserve_edges : ∀ b, Optimization.OnCellEdge slotFloor cellMesh slotTop b →
    Optimization.lowReserveAt price intercept q ≤
        (primeFraction - 1 / 2) * Optimization.planeAmplifier price intercept q lam B b -
          Optimization.planeGap Optimization.slotPrice 1 lam B b / 6 ∧
      Optimization.lowReserveAt price intercept q ≤
        (5 * primeFraction - 1 / 2) * Optimization.planeAmplifier price intercept q lam B b -
          Optimization.planeGap Optimization.slotPrice 1 lam B b / 6 ∧
      Optimization.lowReserveAt price intercept q ≤
        (6 * primeFraction - 1 / 2) * Optimization.planeAmplifier price intercept q lam B b -
          Optimization.planeGap Optimization.slotPrice 1 lam B b / 6
  /-- At the edges of the cell range the main fixed-inducing reserve is at least `1/50` and two thirds of
  `plainLossCap` more. -/
  fixedInducing_edges : ∀ b, Optimization.OnCellEdge slotFloor cellMesh slotTop b →
    1 / 50 + 2 / 3 * plainLossCap ≤ 1 - Optimization.planeTotalLength lam B cellMesh b -
      4 * Optimization.planeAmplifier price intercept q lam B b
  /-- At the edges of the cell range the exceptional reserve is at least `1/50` and two thirds of
  `plainLossCap` more. -/
  exceptional_edges : ∀ b, Optimization.OnCellEdge slotFloor cellMesh slotTop b →
    1 / 50 + 2 / 3 * plainLossCap ≤ 1 - Optimization.planeTotalLength lam B cellMesh b -
      (9 / 2) * Optimization.planeAmplifier price intercept q lam B b
  /-- At the edges of the cell range the second-zero reserve exceeds the amplifier width of the top cell by
  `1/380` and the saving of the second zero. -/
  zero_edges : ∀ b, Optimization.OnCellEdge slotFloor cellMesh slotTop b →
    Optimization.planeAmplifier price intercept q lam B slotTop + 1 / 380 + zeroSaving ≤
      1 - Optimization.planeTotalLength lam B cellMesh b -
        5 * Optimization.planeAmplifier price intercept q lam B b

end Cycle63

namespace Cycle63.AffineLedger

noncomputable section

section Generic

variable [L : AffineLedger]

/-- The amplifier ratio of the step: its amplifier width per unit of gap over the region of its LOW
children. -/
def Ka : ℝ := Optimization.amplifierRatio price intercept q

/-- The gap of the cell `b` over the region of the LOW children. -/
def regionGap (b : ℝ) : ℝ := Optimization.planeGap price intercept lam B b

/-- The gap of the cell `b` over the old region. -/
def g (b : ℝ) : ℝ := Optimization.planeGap Optimization.slotPrice 1 lam B b

/-- The amplifier width of the cell `b`. -/
def amp (b : ℝ) : ℝ := Ka * regionGap b + Optimization.lowReserveWeight

/-- The bound of the total plain and slot length in the cell `b`. -/
def totalA (b : ℝ) : ℝ := Optimization.planeTotalLength lam B cellMesh b

/-- The upper edge of the first cell of the slot window. -/
def firstCellTop : ℝ := slotFloor + cellMesh

/-- The upper edge of the cell `j` of the slot window. -/
def cellUpper (j : ℕ) : ℝ := slotFloor + (j : ℝ) * cellMesh

/-- The original total slot width selects the amplifier once: the first cell whose upper edge is at least
the width. -/
def originalCell (t : ℝ) : ℕ := max 1 ⌈(t - slotFloor) / cellMesh⌉₊

/-- The LOW reserve. -/
def lowReserve : ℝ := Optimization.lowReserveAt price intercept q

/-- The rate at which the LOW half pays the capacity that its deleted slots exceed. -/
def lowRate : ℝ := q / (6 * price)

/-- The smaller value of a function at the two edges of the cell range. -/
def cellMin (f : ℝ → ℝ) : ℝ := min (f firstCellTop) (f slotTop)

/-- The smallest amplifier width on the cell range: the one of the first cell. -/
def amplifierFloor : ℝ := amp firstCellTop

/-- The amplifier width of the top cell of the slot window, the largest of the cells. -/
def amplifierCap : ℝ := amp slotTop

/-- The first error branch's reserve `(primeFraction - 1/2) amp - g/6` on the cell range. -/
def firstErrorReserve : ℝ := cellMin (fun b => (primeFraction - 1 / 2) * amp b - g b / 6)

/-- The sixth error branch's reserve `(5 primeFraction - 1/2) amp - g/6` on the cell range. -/
def sixthErrorReserve : ℝ := cellMin (fun b => (5 * primeFraction - 1 / 2) * amp b - g b / 6)

/-- The seventh error branch's reserve `(6 primeFraction - 1/2) amp - g/6` on the cell range. -/
def seventhErrorReserve : ℝ := cellMin (fun b => (6 * primeFraction - 1 / 2) * amp b - g b / 6)

/-- The second-zero reserve `1 - totalA - 5 amp` on the cell range. -/
def zeroReserve : ℝ := cellMin (fun b => 1 - totalA b - 5 * amp b)

/-- The main fixed-inducing reserve `1 - totalA - 4 amp` on the cell range. -/
def mainFixedReserve : ℝ := cellMin (fun b => 1 - totalA b - 4 * amp b)

/-- The exceptional reserve `1 - totalA - (9/2) amp` on the cell range. -/
def exceptionalReserve : ℝ := cellMin (fun b => 1 - totalA b - (9 / 2) * amp b)

/-- The constant of the prime payment of the main source: `56 (2/a + 12)` at the amplifier floor `a`. -/
def primePaymentConstant : ℝ := 56 * (2 / amplifierFloor + 12)

/-- The amplifier width of the top cell is the amplifier cap. -/
theorem amp_top : amp slotTop = amplifierCap := rfl

theorem q_le_one : q ≤ 1 := q_le_price.trans price_le_one

/-- The plain lengths and the slot sum of a state on the plane together are at most the width. -/
theorem volume_le {M n₁ n₂ z : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z) (h : n₁ + n₂ + lam * z ≤ B * M) :
    n₁ + n₂ + z ≤ M := by
  nlinarith [mul_nonneg (sub_nonneg.mpr one_le_lam) hz, mul_nonneg (sub_nonneg.mpr B_le_one) hM]

/-- The plain lengths `n₁` and `n₂` and the total slot length `z` of a state lie in the window of the ledger. -/
abbrev PlainWindow (n₁ n₂ z : ℝ) : Prop :=
  Optimization.PlainWindow windowBottom sumBottom slotFloor slotTop lam B n₁ n₂ z

/-- A state in the window of the ledger has plain lengths and slot length together of at most one. -/
theorem PlainWindow.volume_le {n₁ n₂ z : ℝ} (h : PlainWindow n₁ n₂ z) (hz : 0 ≤ z) :
    n₁ + n₂ + z ≤ 1 := by
  simpa using Cycle63.AffineLedger.volume_le (M := 1) zero_le_one hz (by simpa using h.plane)

theorem firstCellTop_le_slotTop : firstCellTop ≤ slotTop := by
  have h : (1 : ℝ) ≤ (cellCount : ℝ) := by exact_mod_cast one_le_cellCount
  have hm := cellMesh_pos
  have hc := cellCount_mul
  unfold firstCellTop
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hm.le]

/-- The upper edge of every cell of the slot window lies between the first cell's and the window's top. -/
theorem cellUpper_bounds {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ cellCount) :
    firstCellTop ≤ cellUpper j ∧ cellUpper j ≤ slotTop := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hn : (j : ℝ) ≤ (cellCount : ℝ) := by exact_mod_cast hjn
  have hm := cellMesh_pos
  have hc := cellCount_mul
  unfold cellUpper firstCellTop
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h1 hm.le]
  · nlinarith [mul_le_mul_of_nonneg_right hn hm.le]

/-- The cell of the original slot width exists, lies in the slot window and holds the width between its
lower and upper edge. -/
theorem originalCell_mem {t : ℝ} (ht : slotFloor ≤ t ∧ t ≤ slotTop) :
    1 ≤ originalCell t ∧ originalCell t ≤ cellCount ∧
      cellUpper (originalCell t) - cellMesh ≤ t ∧ t ≤ cellUpper (originalCell t) := by
  have hm := cellMesh_pos
  have hcm := cellCount_mul
  have hx : 0 ≤ (t - slotFloor) / cellMesh := div_nonneg (by linarith [ht.1]) hm.le
  have hxm : (t - slotFloor) / cellMesh * cellMesh = t - slotFloor := div_mul_cancel₀ _ hm.ne'
  have hc : ⌈(t - slotFloor) / cellMesh⌉₊ ≤ cellCount := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hm]
    linarith [ht.2]
  have hle := Nat.le_ceil ((t - slotFloor) / cellMesh)
  have hlt := Nat.ceil_lt_add_one hx
  have hi : 1 ≤ originalCell t := le_max_left _ _
  have hi' : originalCell t ≤ cellCount := max_le one_le_cellCount hc
  refine ⟨hi, hi', ?_, ?_⟩
  · by_cases hc1 : ⌈(t - slotFloor) / cellMesh⌉₊ ≤ 1
    · simp only [originalCell, max_eq_left hc1, cellUpper, Nat.cast_one]
      linarith [ht.1]
    · simp only [originalCell, max_eq_right (by omega : 1 ≤ ⌈(t - slotFloor) / cellMesh⌉₊), cellUpper]
      nlinarith [mul_lt_mul_of_pos_right hlt hm]
  · have hcast : (⌈(t - slotFloor) / cellMesh⌉₊ : ℝ) ≤ (originalCell t : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈(t - slotFloor) / cellMesh⌉₊
    unfold cellUpper
    nlinarith [mul_le_mul_of_nonneg_right (hle.trans hcast) hm.le]

theorem Ka_nonneg : 0 ≤ Ka := by
  unfold Ka Optimization.amplifierRatio
  have h := q_intercept_lt_price
  exact div_nonneg q_pos.le (mul_nonneg (by norm_num) (by linarith))

/-- The amplifier width grows with the cell. -/
theorem amp_slope_nonneg : 0 ≤ Ka * (6 * price - lam) :=
  mul_nonneg Ka_nonneg (sub_nonneg.mpr lam_le_six_price)

theorem amplifierFloor_pos : 0 < amplifierFloor := amp_first_pos

theorem amplifierCap_le_one : amplifierCap ≤ 1 := amp_top_le_one

/-- Bounds of the amplifier width on the cell range: it grows with the cell, from the amplifier floor at the
first cell up to the amplifier cap at the top cell. -/
theorem amp_bounds {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    amplifierFloor ≤ amp b ∧ amp b ≤ amplifierCap := by
  have hslope := amp_slope_nonneg
  constructor
  · unfold amplifierFloor amp regionGap Optimization.planeGap
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hslope]
  · unfold amplifierCap amp regionGap Optimization.planeGap
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hslope]

theorem amp_pos {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : 0 < amp b :=
  amplifierFloor_pos.trans_le (amp_bounds hb).1

theorem amplifierCap_pos : 0 < amplifierCap :=
  amp_pos (b := slotTop) ⟨firstCellTop_le_slotTop, le_rfl⟩

/-- The gap over the old region is positive on the cell range. -/
theorem g_pos {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : 0 < g b := by
  have hc : 0 ≤ 6 * Optimization.slotPrice - lam := sub_nonneg.mpr lam_le_six_slotPrice
  have h0 := oldGap_first_pos
  have hm := mul_le_mul_of_nonneg_left hb.1 hc
  unfold firstCellTop at hm
  unfold Optimization.planeGap at h0
  unfold g Optimization.planeGap
  nlinarith

theorem primePaymentConstant_ge : 56 * (2 / amplifierFloor + 12) ≤ primePaymentConstant := le_rfl

theorem primePaymentConstant_pos : 0 < primePaymentConstant := by
  have h := amplifierFloor_pos
  unfold primePaymentConstant
  positivity

/-- On the cell range an affine function is at least its smaller edge value. -/
theorem cellMin_le (f : ℝ → ℝ) (hf : ∀ b, f b = f 0 + (f 1 - f 0) * b) {b : ℝ}
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : cellMin f ≤ f b := by
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

/-- Both edge values are at least `r`, hence so is `cellMin`. -/
theorem le_cellMin {f : ℝ → ℝ} {r : ℝ} (h₁ : r ≤ f firstCellTop) (h₂ : r ≤ f slotTop) :
    r ≤ cellMin f :=
  le_min h₁ h₂

/-- The first error branch's reserve `(primeFraction - 1/2) amp - g/6` on the cell range. -/
theorem first_error_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    firstErrorReserve ≤ (primeFraction - 1 / 2) * amp b - g b / 6 :=
  cellMin_le (fun b => (primeFraction - 1 / 2) * amp b - g b / 6)
    (fun b => by unfold amp regionGap g Optimization.planeGap; ring) hb

/-- The sixth error branch's reserve `(5 primeFraction - 1/2) amp - g/6` on the cell range. -/
theorem sixth_error_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    sixthErrorReserve ≤ (5 * primeFraction - 1 / 2) * amp b - g b / 6 :=
  cellMin_le (fun b => (5 * primeFraction - 1 / 2) * amp b - g b / 6)
    (fun b => by unfold amp regionGap g Optimization.planeGap; ring) hb

/-- The seventh error branch's reserve `(6 primeFraction - 1/2) amp - g/6` on the cell range. -/
theorem seventh_error_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    seventhErrorReserve ≤ (6 * primeFraction - 1 / 2) * amp b - g b / 6 :=
  cellMin_le (fun b => (6 * primeFraction - 1 / 2) * amp b - g b / 6)
    (fun b => by unfold amp regionGap g Optimization.planeGap; ring) hb

/-- The second-zero reserve `1 - totalA - 5 amp` on the cell range. -/
theorem second_zero_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    zeroReserve ≤ 1 - totalA b - 5 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 5 * amp b)
    (fun b => by unfold totalA amp regionGap Optimization.planeTotalLength Optimization.planeGap; ring) hb

/-- The main fixed-inducing reserve `1 - totalA - 4 amp` on the cell range. -/
theorem main_fixed_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    mainFixedReserve ≤ 1 - totalA b - 4 * amp b :=
  cellMin_le (fun b => 1 - totalA b - 4 * amp b)
    (fun b => by unfold totalA amp regionGap Optimization.planeTotalLength Optimization.planeGap; ring) hb

/-- The exceptional reserve `1 - totalA - (9/2) amp` on the cell range. -/
theorem exceptional_reserve {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    exceptionalReserve ≤ 1 - totalA b - (9 / 2) * amp b :=
  cellMin_le (fun b => 1 - totalA b - (9 / 2) * amp b)
    (fun b => by unfold totalA amp regionGap Optimization.planeTotalLength Optimization.planeGap; ring) hb

theorem lowReserve_pos : 0 < lowReserve := by
  have h : q * intercept / price < 1 := (div_lt_one price_pos).mpr q_intercept_lt_price
  unfold lowReserve Optimization.lowReserveAt
  exact mul_pos Optimization.lowReserveWeight_pos (by linarith)

theorem lowReserve_le : lowReserve ≤ 1 / 50 := lowReserveAt_le

theorem lowRate_mem : 0 < lowRate ∧ lowRate ≤ 1 := by
  have hp := price_pos
  unfold lowRate
  constructor
  · exact div_pos q_pos (by positivity)
  · rw [div_le_one (by positivity)]
    linarith [q_le_price]

/-- The LOW rate is at most `1/6`, since the junction is at most the slot price of the region. -/
theorem lowRate_le_sixth : lowRate ≤ 1 / 6 := by
  have hp := price_pos
  unfold lowRate
  rw [div_le_iff₀ (by positivity)]
  linarith [q_le_price]

/-- The LOW reserve: the intercept and the cell variable cancel. -/
theorem low_reserve (b : ℝ) :
    amp b * (1 - q * intercept / price) - lowRate * regionGap b = lowReserve := by
  have hk : price ≠ 0 := price_pos.ne'
  have hq : price - q * intercept ≠ 0 := (sub_pos.mpr q_intercept_lt_price).ne'
  unfold amp Ka lowRate lowReserve Optimization.lowReserveAt
  exact Optimization.low_reserve_cancel price intercept hk hq (regionGap b) Optimization.lowReserveWeight

/-- The LOW reserve is at most the reserves of the first, sixth and seventh error branches. -/
theorem lowReserve_le_errorReserves :
    lowReserve ≤ firstErrorReserve ∧ lowReserve ≤ sixthErrorReserve ∧
      lowReserve ≤ seventhErrorReserve := by
  have h1 := errorReserve_edges firstCellTop (Or.inl rfl)
  have h2 := errorReserve_edges slotTop (Or.inr rfl)
  exact ⟨le_min h1.1 h2.1, le_min h1.2.1 h2.2.1, le_min h1.2.2 h2.2.2⟩

/-- The main fixed-inducing reserve is at least `1/50` and two thirds of `plainLossCap` more. -/
theorem mainFixedReserve_ge : 1 / 50 + 2 / 3 * plainLossCap ≤ mainFixedReserve :=
  le_cellMin (f := fun b => 1 - totalA b - 4 * amp b)
    (fixedInducing_edges firstCellTop (Or.inl rfl)) (fixedInducing_edges slotTop (Or.inr rfl))

/-- The exceptional reserve is at least `1/50` and two thirds of `plainLossCap` more. -/
theorem exceptionalReserve_ge : 1 / 50 + 2 / 3 * plainLossCap ≤ exceptionalReserve :=
  le_cellMin (f := fun b => 1 - totalA b - (9 / 2) * amp b)
    (exceptional_edges firstCellTop (Or.inl rfl)) (exceptional_edges slotTop (Or.inr rfl))

/-- The second-zero reserve exceeds the amplifier cap by the saving of the second zero and `1/380`. -/
theorem zeroReserve_ge : amplifierCap + 1 / 380 + zeroSaving ≤ zeroReserve :=
  le_cellMin (f := fun b => 1 - totalA b - 5 * amp b)
    (zero_edges firstCellTop (Or.inl rfl)) (zero_edges slotTop (Or.inr rfl))

/-- The slot window and the plane reduce to the gap, the total length and the amplifier width of the cell
that holds the original slot sum. -/
theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0 < M)
    (hz : slotFloor * M ≤ z ∧ z ≤ slotTop * M)
    (haffine : n₁ + n₂ + lam * z ≤ B * M) :
    let j := originalCell (z / M)
    1 ≤ j ∧ j ≤ cellCount ∧
      max (n₁ + n₂ + (6 * Optimization.slotPrice) * z - M) 0 ≤ M * g (cellUpper j) ∧
      n₁ + n₂ + z ≤ M * totalA (cellUpper j) ∧
      0 < M * amp (cellUpper j) := by
  dsimp only
  have ht : slotFloor ≤ z / M ∧ z / M ≤ slotTop :=
    ⟨(le_div_iff₀ hM).mpr hz.1, (div_le_iff₀ hM).mpr hz.2⟩
  obtain ⟨hj1, hj600, hl, hu⟩ := originalCell_mem ht
  have hb := cellUpper_bounds hj1 hj600
  have hzup : z ≤ cellUpper (originalCell (z / M)) * M := (div_le_iff₀ hM).mp hu
  have hzlow : (cellUpper (originalCell (z / M)) - cellMesh) * M ≤ z := (le_div_iff₀ hM).mp hl
  have hcoef : 0 ≤ 6 * Optimization.slotPrice - lam := sub_nonneg.mpr lam_le_six_slotPrice
  have hcoef' : 0 ≤ lam - 1 := sub_nonneg.mpr one_le_lam
  have hdef := mul_le_mul_of_nonneg_left hzup hcoef
  have htotal := mul_le_mul_of_nonneg_left hzlow hcoef'
  have hg := g_pos hb
  have hamp := amp_pos hb
  refine ⟨hj1, hj600, max_le ?_ (mul_pos hM hg).le, ?_, mul_pos hM hamp⟩
  · unfold g Optimization.planeGap
    nlinarith
  · unfold totalA Optimization.planeTotalLength
    nlinarith

end Generic

/-- The LOW children of the step are deleted into the old region: the slot price and the intercept of their
region are the old region's. -/
class DeletesIntoOldRegion [L : AffineLedger] : Prop where
  /-- The slot price of the region of the LOW children is the old region's. -/
  price_eq : price = Optimization.slotPrice
  /-- The intercept of the region of the LOW children is the old region's. -/
  intercept_eq : intercept = 1

section OldRegion

variable [L : AffineLedger] [DeletesIntoOldRegion]

theorem price_eq_slotPrice : price = Optimization.slotPrice := DeletesIntoOldRegion.price_eq

theorem intercept_eq_one : intercept = 1 := DeletesIntoOldRegion.intercept_eq

/-- The gap over the region of the LOW children is the gap over the old region. -/
theorem regionGap_eq_g (b : ℝ) : regionGap b = g b := by
  unfold regionGap g
  rw [price_eq_slotPrice, intercept_eq_one]

/-- The LOW rate is `q/(6 κ)` for the slot price `κ` of the old region. -/
theorem lowRate_eq : lowRate = q / (6 * Optimization.slotPrice) := by
  unfold lowRate
  rw [price_eq_slotPrice]

/-- The LOW reserve is `α (1 - q/κ)` for the slot price `κ` of the old region. -/
theorem lowReserve_eq :
    lowReserve = Optimization.lowReserveWeight * (1 - q / Optimization.slotPrice) := by
  unfold lowReserve Optimization.lowReserveAt
  rw [price_eq_slotPrice, intercept_eq_one, mul_one]

/-- The LOW rate pays the six-amplifier overshoot of the LOW children over the old region down to the LOW
reserve. -/
theorem low_reserve_old (b : ℝ) : amp b - lowRate * (g b + 6 * amp b) = lowReserve := by
  have h := low_reserve b
  rw [intercept_eq_one, regionGap_eq_g, mul_one] at h
  have h6 : lowRate * 6 = q / price := by
    unfold lowRate
    rw [div_mul_eq_mul_div, mul_comm q 6, mul_div_mul_left q price (by norm_num : (6 : ℝ) ≠ 0)]
  rw [← h]
  linear_combination (-(amp b)) * h6

end OldRegion

end

end Cycle63.AffineLedger

end Record1252270103Bootstrap.PR67
