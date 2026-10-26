import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.LocalReserves
import Mathlib.Tactic.FieldSimp

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Physical_Capacity : Cycle63.AffineLedger := Cycle153.Root.rootLedger


/-! The plain length, the affine slot capacity and the shift reserve of the reflected numerator rows
with row length `d ∈ [dMinus, dPlus]` and shift `t ∈ [0, t0]`.

The window conditions are stated with their exact limits: the plain length lies in
`(windowBottom, plainTop)`, the slot capacity lies above `slotFloor` and below `smallPlainCap`, the largest
width for which the old capacity holds below the window, and the shift reserve at the largest shift
base keeps the proportional part `reserveProportion * t`. Inequalities between the constants are proved from their
interval enclosures (`bracket`), those over the row length by `rat_pos`. -/

namespace Cycle153Endpoint.Physical

open Arithmetic

noncomputable section

def plainScale (d t : ℝ) : ℝ := 1 - y / d + t
def affineCapacity (d t : ℝ) : ℝ := (B - 2 * plainScale d t) / lambda
def shiftBase (d : ℝ) : ℝ := 2 * y / d - 1
def oldCapacity (b t : ℝ) : ℝ := max 0 ((b - 2 * t) / (9 / 2))
def shiftReserve (b t : ℝ) : ℝ :=
  t / 2 - (1 / 4) * ((b - (1 - B)) / lambda - oldCapacity b t)

/-- An enclosure of the largest plain length `1 - y/dPlus + t0`. -/
bracket plainScaleTop_bounds (digits := 12) : 1 - y / dPlus + t0
  using [h_enclosure, dPlusOffset_bounds, t0_bounds] unfolding [y, ell, theta, dPlus]

/-- An enclosure of the smallest slot capacity, the one at the largest plain length. -/
bracket affineCapacityLow_bounds (digits := 12) : (B - 2 * (1 - y / dPlus + t0)) / lambda
  using [B_enclosure, lambda_enclosure, plainScaleTop_bounds] unfolding []

/-- An enclosure of the slot supply left at the largest row length and the largest capacity. -/
bracket supplyLeft_bounds (digits := 12) : ell - dPlus * ((B - 2 * (1 - y / dMinus)) / lambda)
  using [B_enclosure, lambda_enclosure, h_enclosure, dPlusOffset_bounds, dMinus_bounds]
  unfolding [ell, theta, dPlus, y]

theorem physical_d_pos {d : ℝ} (hd : dMinus ≤ d) : 0 < d := by
  have := half_lt_dMinus
  linarith

theorem y_pos : 0 < y := by
  have hh := h_bounds
  unfold y
  norm_num [ell, theta]
  linarith [hh.1]

/-- The plain length grows with the row length and with the shift. -/
theorem plainScale_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    1 - y / dMinus ≤ plainScale d t ∧ plainScale d t ≤ 1 - y / dPlus + t0 := by
  have hdm : 0 < dMinus := physical_d_pos le_rfl
  have hdp := physical_d_pos hd.1
  have hhi := div_le_div_of_nonneg_left y_pos.le hdm hd.1
  have hlo := div_le_div_of_nonneg_left y_pos.le hdp hd.2
  unfold plainScale
  constructor <;> linarith [ht.1, ht.2]

theorem plainScale_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    Cycle153Endpoint.CountAffine.windowBottom < plainScale d t ∧ plainScale d t < Cycle153Endpoint.CountAffine.plainTop := by
  have hn := plainScale_bounds hd ht
  have hh := h_bounds
  have hdm := dMinus_bounds
  have hlo : Cycle153Endpoint.CountAffine.windowBottom < 1 - y / dMinus := by
    unfold y ell theta Cycle153Endpoint.CountAffine.windowBottom
    rat_pos [hh, hdm]
  have hhi : 1 - y / dPlus + t0 < Cycle153Endpoint.CountAffine.plainTop := by
    have := plainScaleTop_bounds.2
    unfold Cycle153Endpoint.CountAffine.plainTop
    linarith
  constructor <;> linarith [hn.1, hn.2]

/-- The slot capacity is decreasing in the plain length. -/
theorem affineCapacity_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    (B - 2 * (1 - y / dPlus + t0)) / lambda ≤ affineCapacity d t ∧
      affineCapacity d t ≤ (B - 2 * (1 - y / dMinus)) / lambda := by
  have hn := plainScale_bounds hd ht
  unfold affineCapacity
  constructor
  · apply div_le_div_of_nonneg_right _ lambda_pos.le; linarith [hn.2]
  · apply div_le_div_of_nonneg_right _ lambda_pos.le; linarith [hn.1]

theorem affineCapacity_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    Cycle153.Root.floor < affineCapacity d t ∧ affineCapacity d t ≤ smallPlainCap := by
  have hz := affineCapacity_bounds hd ht
  have hlo : Cycle153.Root.floor < (B - 2 * (1 - y / dPlus + t0)) / lambda := by
    have := affineCapacityLow_bounds.1
    unfold Cycle153.Root.floor
    linarith
  have hhi : (B - 2 * (1 - y / dMinus)) / lambda ≤ smallPlainCap := by
    have hl := lambda_pos
    have hy := y_pos
    have hden : 0 < lambda * smallPlainCap + 2 - B := by
      have := B_bounds.2
      unfold smallPlainCap CountAffine.windowBottom CountAffine.plainTop
      nlinarith
    have hyne : y ≠ 0 := hy.ne'
    have h1 : y / dMinus = (lambda * smallPlainCap + 2 - B) / 2 := by
      unfold dMinus
      rw [div_div_eq_mul_div]
      field_simp
    apply le_of_eq
    rw [h1]
    field_simp
    ring
  constructor <;> linarith [hz.1, hz.2]

theorem affineCapacity_budget (d t : ℝ) :
    2 * plainScale d t + lambda * affineCapacity d t = B := by
  unfold affineCapacity
  field_simp [lambda_pos.ne']
  ring

theorem scaled_capacity_zero {d : ℝ} (hd : d ≠ 0) :
    d * affineCapacity d 0 = (2 * y - (2 - B) * d) / lambda := by
  unfold affineCapacity plainScale
  field_simp [hd, lambda_pos.ne']
  ring

theorem affineCapacity_shift (d t : ℝ) :
    affineCapacity d 0 - affineCapacity d t = 2 * t / lambda := by
  unfold affineCapacity plainScale
  ring

theorem small_slot_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ Cycle153Endpoint.CountAffine.plainTop) (h2 : n2 ≤ Cycle153Endpoint.CountAffine.plainTop) (hz : z ≤ Cycle153.Root.floor) :
    n1 + n2 + (9 / 2) * z ≤ 1 := by
  have := small_slot_complement
  linarith

theorem small_plain_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ Cycle153Endpoint.CountAffine.windowBottom) (h2 : n2 ≤ Cycle153Endpoint.CountAffine.plainTop) (hz : z ≤ smallPlainCap) :
    n1 + n2 + (9 / 2) * z ≤ 1 := by
  unfold smallPlainCap at hz
  linarith

theorem affine_shortening {d t n1 n2 z : ℝ}
    (h1 : n1 ≤ plainScale d t) (h2 : n2 ≤ plainScale d t)
    (hz : z ≤ affineCapacity d t) : n1 + n2 + lambda * z ≤ B := by
  have hmul := mul_le_mul_of_nonneg_left hz (le_of_lt lambda_pos)
  have := affineCapacity_budget d t
  linarith

theorem positive_supply {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    4 / 21 < ell / d := by
  have hy : 0 ≤ ell := le_of_lt ell_pos
  have hdiv := div_le_div_of_nonneg_left hy (physical_d_pos hd.1) hd.2
  have := supply_lower
  linarith

/-- The slot capacity never uses the whole slot supply `ell`. -/
theorem capacity_supply {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    0 ≤ ell - d * affineCapacity d t := by
  have hz := affineCapacity_bounds hd ht
  have hzp : 0 ≤ affineCapacity d t := by
    linarith [(affineCapacity_interior hd ht).1, Cycle153Endpoint.Arithmetic.slotFloor_pos]
  have hdp : 0 ≤ dPlus := (physical_d_pos hd.1).le.trans hd.2
  have hprod := mul_le_mul hd.2 hz.2 hzp hdp
  have hsup := supplyLeft_bounds.1
  linarith

theorem shiftBase_bounds {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    0 ≤ shiftBase d ∧ shiftBase d ≤ shiftBase dMinus ∧ shiftBase dMinus ≤ 1 / 5 := by
  have hdm : 0 < dMinus := physical_d_pos le_rfl
  have hdp := physical_d_pos hd.1
  have hh := h_bounds
  have hhi := div_le_div_of_nonneg_left (by linarith [y_pos] : 0 ≤ 2 * y) hdm hd.1
  have hoff := dPlusOffset_bounds
  have hlow : 0 < 2 * y / dPlus - 1 := by
    unfold y dPlus ell theta
    rat_pos [hh, hoff]
  have hlo := div_le_div_of_nonneg_left (by linarith [y_pos] : 0 ≤ 2 * y) hdp hd.2
  have hdm' := dMinus_bounds
  have htop : 2 * y / dMinus - 1 < 1 / 5 := by
    unfold y ell theta
    rat_pos [hh, hdm']
  unfold shiftBase
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem shiftReserve_unclipped {b t : ℝ} (ht : 2 * t ≤ b) :
    shiftReserve b t = (7 / 18) * t + b / 18 - (b - (1 - B)) / (4 * lambda) := by
  have hnonneg : 0 ≤ (b - 2 * t) / (9 / 2) := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_right hnonneg]
  field_simp [lambda_pos.ne']
  ring

theorem shiftReserve_clipped {b t : ℝ} (ht : b ≤ 2 * t) :
    shiftReserve b t = t / 2 - (b - (1 - B)) / (4 * lambda) := by
  have hnonpos : (b - 2 * t) / (9 / 2) ≤ 0 := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_left hnonpos]
  field_simp [lambda_pos.ne']
  ring

theorem oldCapacity_nonneg (b t : ℝ) : 0 ≤ oldCapacity b t := le_max_left _ _

theorem large_shift_reserve {b t : ℝ} (hb : b ≤ shiftBase dMinus) (ht : t0 ≤ t) :
    reserveProportion * t ≤ shiftReserve b t := by
  have hl := lambda_bounds
  have hlam : 0 < lambda := by linarith [hl.1]
  have hB1 : B < 1 := by linarith [B_bounds.2]
  have ht0 : (0 : ℝ) < t0 := lt_of_lt_of_le (by norm_num) t0_bounds.1
  have htp : 0 < t := lt_of_lt_of_le ht0 ht
  by_cases hclip : b ≤ 2 * t
  · rw [shiftReserve_clipped hclip]
    have hnum : b - (1 - B) ≤ 2 * t := by linarith
    have hfrac : (b - (1 - B)) / (4 * lambda) ≤ t / 7 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hl.1 htp.le]
    have hshare : reserveProportion * t ≤ t / 500 := by
      norm_num [reserveProportion, dampingRate, Cycle63.Optimization.allowanceUnit]
      linarith
    linarith
  · have hu : 2 * t ≤ b := le_of_lt (lt_of_not_ge hclip)
    rw [shiftReserve_unclipped hu]
    have hq := q0_bounds
    have hh := h_bounds
    have hcoef : 1 / 18 - 1 / (4 * lambda) < 0 := by
      rw [sub_neg, div_lt_div_iff₀ (by norm_num) (by positivity)]
      linarith [hl.2]
    -- `t0` is the shift at which the reserve at the largest base equals its proportional part.
    have hcorner : 0 ≤ (7 / 18 - reserveProportion) * t0 + shiftBase dMinus * (1 / 18 - 1 / (4 * lambda))
        + (1 - B) / (4 * lambda) := by
      apply le_of_eq
      have hd : dMinus ≠ 0 := (physical_d_pos le_rfl).ne'
      unfold t0 reserveProportion dampingRate Cycle63.Optimization.allowanceUnit shiftBase
      field_simp
      ring
    have hid : (7 / 18) * t + b / 18 - (b - (1 - B)) / (4 * lambda) - reserveProportion * t =
        (7 / 18 - reserveProportion) * t + b * (1 / 18 - 1 / (4 * lambda)) + (1 - B) / (4 * lambda) := by
      field_simp
      ring
    have hb' := mul_le_mul_of_nonpos_right hb hcoef.le
    have hshare : (0 : ℝ) ≤ 7 / 18 - reserveProportion := by
      norm_num [reserveProportion, dampingRate, Cycle63.Optimization.allowanceUnit]
    nlinarith [mul_le_mul_of_nonneg_left ht hshare]

end

end Cycle153Endpoint.Physical
