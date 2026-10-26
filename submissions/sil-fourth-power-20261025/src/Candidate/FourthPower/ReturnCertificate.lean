/- Copyright (c) 2026 Sil. Apache-2.0.
Exact complementary return certificate and its continuous scalar consequences.
The finite count-admission and 86-rectangle certificate is a separate obligation;
this file does not postulate that certificate or an analytical source theorem. -/
import Candidate.FourthPower.Parameters

set_option autoImplicit false

namespace Candidate.FourthPower.ReturnCertificate
noncomputable section

def mMinus : ℝ := 2 / 5
def mPlus : ℝ := 11 / 25
def sMinus : ℝ := 17 / 500
def sPhysical : ℝ := 1 / 25
def shiftCutoff : ℝ := 1 / 250
def incumbentCost : ℝ := 6 * (2 * incumbent - 1)
def mHigh : ℝ := (1 - incumbentCost * sMinus) / 2
def plainLower : ℝ := 1 - y / ds
def plainUpper : ℝ := 1 - y / dplus + shiftCutoff
def widthLower : ℝ := min sPhysical ((physicalIntercept - 2 * plainUpper) / physicalSlope)
def floorValue (d : ℝ) : ℝ :=
  (4 / 25) * x - 3 / 20 - (51 / 100) * y + (67 / 100) * d - (3 / 20) * ell
def largeShiftReserve : ℝ :=
  (7 / 18 - 1 / 500) * shiftCutoff + (1 - physicalIntercept) / 18 +
    (physicalSlope / 18 - 1 / 4) * sPhysical
def shiftSlope : ℝ := 1 / 2 - 1 / 500 - 1 / (2 * physicalSlope)

/-- All complementary scalar guards in the independent exact receipt. -/
structure ComplementaryGuards : Prop where
  gram_x : 0 < x - ell
  gram_y : 0 < y - x
  gram_ell : 0 < 1 / 5 - ell
  gram_two_x : 0 < 2 * x - y - ell
  conductor_first : 0 < y - d0
  conductor_second : 0 < ds - y
  conductor_third : 0 < dk - ds
  conductor_last : 0 < dplus - dk
  conductor_double : 0 < 2 * y - dplus
  plain_lower : 0 < plainLower - mMinus - eta
  plain_upper : 0 < mPlus - plainUpper - eta
  width_lower : 0 < widthLower - sMinus - eta
  width_upper : 0 < 43 / 1000 - sPhysical - eta
  large_shift : eta < largeShiftReserve
  small_shift : 0 < shiftSlope
  supply : 0 < ell / dplus - 1 / 5
  capacity : 0 < y / dplus - 1 / 2
  incumbent_margin : 0 < incumbent - theta
  feedback_k : 0 < kappa - 7 / 10
  feedback_d : 0 < 1 - dplus
  feedback_y : 0 < 1 / 2 - y
  feedback_cost : 0 < (1 / 8 : ℝ) - 5 / 288 - 25 / 784
  floor_guard : 0 < theta - (4 + y - x) / 6 - 1 / 200 - floorValue dplus
  small_row : 0 < -(1 / 20 : ℝ) - (13 * h / 75 - y / 2 + (63 / 50) * d0)
  principal_width : 0 < y / 20 - (1 + h) / 1000 - 1 / 4000
  principal_conductor : 0 < h / 600 - 1 / 1000 - 1 / 4000
  holomorphic : 0 < theta - 17 / 20
  slope_lower : 0 < physicalSlope - 3
  intercept_upper : 0 < 1 - physicalIntercept
  slope_upper : 0 < 9 / 2 - physicalSlope
  count_cap : 0 < 549989 / 10000000 - countFace.cap
  source_zero : 0 < sourceB - physicalIntercept
  source_cap : 0 < sourceB - physicalIntercept -
    (sourceSlope - physicalSlope) * (43 / 1000)

theorem complementary_guards : ComplementaryGuards := by
  constructor <;>
    norm_num [plainLower, plainUpper, widthLower, floorValue, largeShiftReserve,
      shiftSlope, mMinus, mPlus, sMinus, sPhysical, shiftCutoff,
      physical_intercept_exact, physicalSlope, countFace, sourceB, sourceSlope,
      ds, dk, dplus, d0, eta, x, y, ell, kappa, theta, h, incumbent]

/-- The very small final conductor interval is positive without spending eta. -/
theorem last_conductor_margin :
    dplus - dk = 10087380243 / 138202430000000000 := by
  norm_num [dplus, dk, physical_intercept_exact, physicalSlope, y, ell, theta, h]

theorem tail_parameters :
    0 < incumbentCost ∧ mMinus + eta < mHigh ∧ mHigh + eta < mPlus ∧
    sMinus + eta < sPhysical ∧ sPhysical < 43 / 1000 - eta ∧
    0 < shiftCutoff ∧ 0 < eta ∧ 0 < reserve := by
  norm_num [incumbentCost, incumbent, mHigh, mMinus, mPlus, eta,
    sMinus, sPhysical, shiftCutoff, reserve]

def shiftedPlain (d t : ℝ) : ℝ := 1 - y / d + t
def shiftedWidth (d t : ℝ) : ℝ :=
  min sPhysical ((physicalIntercept - 2 * shiftedPlain d t) / physicalSlope)

theorem shifted_plain_bounds {d t : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff) :
    plainLower ≤ shiftedPlain d t ∧ shiftedPlain d t ≤ plainUpper := by
  have hds : 0 < ds := by
    rw [joins_exact.1]
    norm_num
  have hdp : 0 < dplus := by
    rw [joins_exact.2.2]
    norm_num
  have hdpos : 0 < d := hds.trans_le hd
  have hy : 0 ≤ y := by rw [parameters_exact.2.2.2]; norm_num
  have hlo : y / d ≤ y / ds := by
    apply (div_le_div_iff₀ hdpos hds).2
    exact mul_le_mul_of_nonneg_left hd hy
  have hhi : y / dplus ≤ y / d := by
    apply (div_le_div_iff₀ hdp hdpos).2
    exact mul_le_mul_of_nonneg_left hd' hy
  dsimp [plainLower, plainUpper, shiftedPlain]
  constructor <;> linarith

theorem shifted_plain_window {d t : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff) :
    mMinus + eta < shiftedPlain d t ∧ shiftedPlain d t < mPlus - eta := by
  have hb := shifted_plain_bounds hd hd' ht ht'
  have hlo := complementary_guards.plain_lower
  have hhi := complementary_guards.plain_upper
  constructor <;> linarith

theorem shifted_width_bounds {d t : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff) :
    widthLower ≤ shiftedWidth d t ∧ shiftedWidth d t ≤ sPhysical := by
  have hp := (shifted_plain_bounds hd hd' ht ht').2
  have hL : 0 < physicalSlope := by norm_num [physicalSlope]
  constructor
  · dsimp [widthLower, shiftedWidth]
    apply min_le_min_left
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hL)
  · exact min_le_left _ _

theorem shifted_width_window {d t : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff) :
    sMinus + eta < shiftedWidth d t ∧ shiftedWidth d t < 43 / 1000 - eta := by
  have hb := shifted_width_bounds hd hd' ht ht'
  have hlo := complementary_guards.width_lower
  have hhi := complementary_guards.width_upper
  constructor <;> linarith

/-- The selected equal-plain shifted point satisfies the physical source face. -/
theorem shifted_source_budget (d t : ℝ) :
    2 * shiftedPlain d t + physicalSlope * shiftedWidth d t ≤ physicalIntercept := by
  have hL : 0 < physicalSlope := by norm_num [physicalSlope]
  have hz : shiftedWidth d t ≤
      (physicalIntercept - 2 * shiftedPlain d t) / physicalSlope := min_le_right _ _
  have hz' := (le_div_iff₀ hL).1 hz
  nlinarith

/-- Thus all small reflected shifts lie in the already proved downward source domain. -/
theorem shifted_global_source_domain {d t : ℝ}
    (hd : ds ≤ d) (hd' : d ≤ dplus) (ht : 0 ≤ t) (ht' : t ≤ shiftCutoff) :
    0 < shiftedPlain d t ∧ 0 < shiftedWidth d t ∧
    shiftedWidth d t ≤ sourceCap ∧
    2 * shiftedPlain d t + sourceSlope * shiftedWidth d t ≤ sourceB := by
  have hp := shifted_plain_window hd hd' ht ht'
  have hw := shifted_width_window hd hd' ht ht'
  have hp0 : 0 < shiftedPlain d t := by
    norm_num [mMinus, eta] at hp
    linarith
  have hw0 : 0 < shiftedWidth d t := by
    norm_num [sMinus, eta] at hw
    linarith
  have hcap : shiftedWidth d t ≤ physicalFace.cap := by
    dsimp [physicalFace]
    have he : 0 < eta := by norm_num [eta]
    linarith [hw.2]
  have hs := Face.source_domain physicalFace_included (le_of_lt hw0) hcap
    (shifted_source_budget d t)
  exact ⟨hp0, hw0, hs⟩

private theorem min_loss (c a v : ℝ) (hv : 0 ≤ v) :
    0 ≤ min c a - min c (a-v) ∧ min c a - min c (a-v) ≤ v := by
  rcases le_total c a with ha | ha
  · rw [min_eq_left ha]
    rcases le_total c (a-v) with hb | hb
    · rw [min_eq_left hb]
      constructor <;> linarith
    · rw [min_eq_right hb]
      constructor <;> linarith
  · rw [min_eq_right ha, min_eq_right (by linarith : a-v ≤ c)]
    constructor <;> linarith

/-- The physical cap is Lipschitz under arbitrary nonnegative shortening. -/
theorem shifted_width_loss (d : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ shiftedWidth d 0 - shiftedWidth d t ∧
    shiftedWidth d 0 - shiftedWidth d t ≤ 2 * t / physicalSlope := by
  have hL : 0 < physicalSlope := by norm_num [physicalSlope]
  have h := min_loss sPhysical ((physicalIntercept - 2 * shiftedPlain d 0) / physicalSlope)
    (2*t/physicalSlope) (div_nonneg (by linarith) (le_of_lt hL))
  have he : (physicalIntercept - 2 * shiftedPlain d t) / physicalSlope =
      (physicalIntercept - 2 * shiftedPlain d 0) / physicalSlope - 2*t/physicalSlope := by
    dsimp [shiftedPlain]
    ring
  simpa only [shiftedWidth, he] using h

/-- A uniform scalar saving; no count or moment estimate is a hypothesis. -/
theorem small_shift_saving (d : ℝ) {δ q t : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hqp : q ≤ δ / 2) (ht : 0 ≤ t) :
    δ * t / 500 ≤ δ * t / 2 - q / 2 * (shiftedWidth d 0 - shiftedWidth d t) := by
  have hl := (shifted_width_loss d ht).2
  have hprod := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ q/2)
  have hqt := mul_le_mul_of_nonneg_right hqp ht
  have hdt : 0 ≤ δ*t := mul_nonneg hδ ht
  norm_num [physicalSlope] at hprod
  nlinarith

def widthAt (b : ℝ) : ℝ :=
  min sPhysical ((b - (1 - physicalIntercept)) / physicalSlope)

/-- The minimum in the old positive-width branch is at the physical-cap corner.
This inequality is valid for every real b, so it imposes no artificial upper cap. -/
theorem large_shift_corner (b : ℝ) :
    (1 - physicalIntercept) / 18 +
      (physicalSlope / 18 - 1 / 4) * sPhysical ≤ b / 18 - widthAt b / 4 := by
  have hcap : widthAt b ≤ sPhysical := min_le_left _ _
  have hline : widthAt b ≤ (b - (1 - physicalIntercept)) / physicalSlope := min_le_right _ _
  norm_num [physicalSlope] at hline ⊢
  nlinarith

theorem large_shift_saving {b t : ℝ} (ht : shiftCutoff ≤ t) :
    eta < (7 / 18 - 1 / 500) * t + b / 18 - widthAt b / 4 := by
  have hc := large_shift_corner b
  have hg := complementary_guards.large_shift
  dsimp [largeShiftReserve] at hg
  linarith

/-- The clipped old-width branch has a positive reserve even for arbitrary b. -/
theorem clipped_shift_saving {b t : ℝ} (ht : 0 ≤ t) (hb : b ≤ 2*t) :
    0 < t / 2 - widthAt b / 4 - t / 500 := by
  have hz : widthAt b ≤ (b - (1 - physicalIntercept)) / physicalSlope := min_le_right _ _
  have hB := complementary_guards.intercept_upper
  norm_num [physicalSlope] at hz
  nlinarith

def oldCapacity (k d : ℝ) : ℝ := min d (2*y-d) / (6*k)
def newCapacity (d : ℝ) : ℝ :=
  min (sPhysical*d) ((2*y-(2-physicalIntercept)*d)/physicalSlope)

theorem old_capacity_left {k d : ℝ} (hd : d ≤ y) :
    oldCapacity k d = d/(6*k) := by
  rw [oldCapacity, min_eq_left (by linarith : d ≤ 2*y-d)]

theorem old_capacity_right {k d : ℝ} (hd : y ≤ d) :
    oldCapacity k d = (2*y-d)/(6*k) := by
  rw [oldCapacity, min_eq_right (by linarith : 2*y-d ≤ d)]

theorem new_capacity_left {d : ℝ} (hd : d ≤ dk) :
    newCapacity d = sPhysical*d := by
  apply min_eq_left
  norm_num [sPhysical, physicalSlope, physical_intercept_exact, y, ell, theta, h,
    dk] at hd ⊢
  linarith

theorem new_capacity_right {d : ℝ} (hd : dk ≤ d) :
    newCapacity d = (2*y-(2-physicalIntercept)*d)/physicalSlope := by
  apply min_eq_right
  norm_num [sPhysical, physicalSlope, physical_intercept_exact, y, ell, theta, h,
    dk] at hd ⊢
  linarith

theorem capacity_joins :
    oldCapacity kappa ds = sPhysical*ds ∧ newCapacity ds = sPhysical*ds ∧
    newCapacity dk = sPhysical*dk := by
  have hys := conductor_order.2.1
  have hsk := conductor_order.2.2.1
  constructor
  · rw [old_capacity_right hys.le]
    norm_num [sPhysical, ds, y, ell, kappa, theta, h]
  constructor
  · exact new_capacity_left hsk.le
  · exact new_capacity_left le_rfl

def returnValue (d C δ p R : ℝ) : ℝ :=
  1/2 + 13*h/75-y/2-ell/2-(9/100)*d+δ/2+
    δ*p*(ell-C/2)+(3/4)*d*R

/-- The count-envelope value R is held fixed throughout interpolation. -/
theorem return_affine (d₁ d₂ C₁ C₂ δ p R u : ℝ) :
    returnValue ((1-u)*d₁+u*d₂) ((1-u)*C₁+u*C₂) δ p R =
      (1-u)*returnValue d₁ C₁ δ p R + u*returnValue d₂ C₂ δ p R := by
  dsimp [returnValue]
  ring

theorem interpolate_return {d₁ d₂ C₁ C₂ δ p R u B : ℝ}
    (hu : 0 ≤ u) (hu' : u ≤ 1)
    (h₁ : returnValue d₁ C₁ δ p R ≤ B)
    (h₂ : returnValue d₂ C₂ δ p R ≤ B) :
    returnValue ((1-u)*d₁+u*d₂) ((1-u)*C₁+u*C₂) δ p R ≤ B := by
  rw [return_affine]
  have h₁' := mul_le_mul_of_nonneg_left h₁ (by linarith : 0 ≤ 1-u)
  have h₂' := mul_le_mul_of_nonneg_left h₂ hu
  nlinarith

/-- Clearing the positive count denominator preserves the return reserve. -/
theorem return_from_cleared {d C δ p R N J : ℝ}
    (hd : 0 ≤ d) (hJ : 0 < J) (hR : R ≤ N/J)
    (hpoly : 0 ≤ J*(theta-reserve-returnValue d C δ p 0)-(3/4)*d*N) :
    returnValue d C δ p R ≤ theta-reserve := by
  have hRJ : R*J ≤ N := (le_div_iff₀ hJ).1 hR
  have hcost := mul_le_mul_of_nonneg_left hRJ (by linarith : 0 ≤ (3/4)*d)
  have he : returnValue d C δ p R = returnValue d C δ p 0+(3/4)*d*R := by
    dsimp [returnValue]
    ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left hJ).mp
  nlinarith

end
end Candidate.FourthPower.ReturnCertificate
