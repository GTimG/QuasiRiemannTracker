import Candidate.Cycle63.Arithmetic.LocalReserves
import Mathlib.Tactic.FieldSimp

/- Original module: Candidate.Cycle63.Physical.Capacity. -/
section

namespace Cycle63.Physical

open Arithmetic

noncomputable section

def plainScale (d t : ℝ) : ℝ := 1 - y / d + t
def affineCapacity (d t : ℝ) : ℝ := (B - 2 * plainScale d t) / lambda
def shiftBase (d : ℝ) : ℝ := 2 * y / d - 1
def oldCapacity (b t : ℝ) : ℝ := max 0 ((b - 2 * t) / (9 / 2))
def shiftReserve (b t : ℝ) : ℝ :=
  t / 2 - (1 / 4) * ((b - (1 - B)) / lambda - oldCapacity b t)

theorem physical_d_pos {d : ℝ} (hd : dMinus ≤ d) : 0 < d := by
  have := half_lt_dMinus
  linarith

theorem plainScale_exact_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    25051/59625 ≤ plainScale d t ∧
      plainScale d t ≤ 10062268003003/23868000003000 := by
  have hy : 0 ≤ y := by norm_num [y]
  have hdm : 0 < dMinus := by norm_num [dMinus]
  have hdp := physical_d_pos hd.1
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy hdp hd.2
  norm_num [y, dMinus, dPlus, t0, plainScale] at *
  constructor <;> linarith

theorem plainScale_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    41 / 100 < plainScale d t ∧ plainScale d t < 264 / 625 := by
  have hn := plainScale_exact_bounds hd ht
  constructor <;> linarith

theorem affineCapacity_exact_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    55730084782197769/1536462720193120000 ≤ affineCapacity d t ∧
      affineCapacity d t ≤ 200407169/5418720000 := by
  have hn := plainScale_exact_bounds hd ht
  unfold affineCapacity
  norm_num [B, lambda] at *
  constructor <;> linarith

theorem affineCapacity_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    17 / 500 < affineCapacity d t ∧ affineCapacity d t < 37 / 1000 := by
  have hz := affineCapacity_exact_bounds hd ht
  constructor <;> linarith

theorem affineCapacity_budget (d t : ℝ) :
    2 * plainScale d t + lambda * affineCapacity d t = B := by
  unfold affineCapacity
  norm_num [lambda]
  ring

theorem scaled_capacity_zero {d : ℝ} (hd : d ≠ 0) :
    d * affineCapacity d 0 = (2 * y - (2 - B) * d) / lambda := by
  unfold affineCapacity plainScale
  field_simp [hd]
  ring

theorem affineCapacity_shift (d t : ℝ) :
    affineCapacity d 0 - affineCapacity d t = 2 * t / lambda := by
  unfold affineCapacity plainScale
  ring

theorem small_slot_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 264 / 625) (h2 : n2 ≤ 264 / 625) (hz : z ≤ 17 / 500) :
    n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 5000 := by
  have := small_slot_complement
  linarith

theorem small_plain_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 41 / 100) (h2 : n2 ≤ 264 / 625) (hz : z ≤ 37 / 1000) :
    n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 10000 := by
  have := small_plain_complement
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

theorem capacity_supply {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    7471440371235592831/54187200000000000000 ≤
      ell - d * affineCapacity d t := by
  have hz := affineCapacity_exact_bounds hd ht
  have hzp : 0 ≤ affineCapacity d t := by linarith
  have hdp : 0 ≤ dPlus := by norm_num [dPlus]
  have hprod := mul_le_mul hd.2 hz.2 hzp hdp
  norm_num [dPlus, ell] at *
  linarith

theorem small_shift_paid {t q delta : ℝ}
    (ht : 0 ≤ t) (hq : q ≤ delta / 2) (hd : 0 ≤ delta) :
    t * q / lambda ≤ delta * t / 2 := by
  have hmul := mul_le_mul_of_nonneg_left hq ht
  have hnonneg : 0 ≤ delta * t := mul_nonneg hd ht
  norm_num [lambda] at *
  nlinarith

theorem shiftBase_bounds {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    0 ≤ shiftBase d ∧ shiftBase d ≤ 9523/59625 ∧
      shiftBase d < 4 / 25 := by
  have hy : 0 ≤ y := by norm_num [y]
  have hdm : 0 < dMinus := by norm_num [dMinus]
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy (physical_d_pos hd.1) hd.2
  have hi_eq : y / dMinus = 34574/59625 := by norm_num [y, dMinus]
  have lo_eq : y / dPlus = 13829600000/23868000003 := by norm_num [y, dPlus]
  rw [hi_eq] at hhi
  rw [lo_eq] at hlo
  have base_eq : shiftBase d = 2 * (y / d) - 1 := by unfold shiftBase; ring
  rw [base_eq]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem shiftReserve_unclipped {b t : ℝ} (ht : 2 * t ≤ b) :
    shiftReserve b t = (7 / 18) * t + b / 18 - (b - (1 - B)) / (4 * lambda) := by
  have hnonneg : 0 ≤ (b - 2 * t) / (9 / 2) := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_right hnonneg]
  ring

theorem shiftReserve_clipped {b t : ℝ} (ht : b ≤ 2 * t) :
    shiftReserve b t = t / 2 - (b - (1 - B)) / (4 * lambda) := by
  have hnonpos : (b - 2 * t) / (9 / 2) ≤ 0 := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_left hnonpos]
  ring

theorem oldCapacity_nonneg (b t : ℝ) : 0 ≤ oldCapacity b t := le_max_left _ _

theorem oldCapacity_zero {b t : ℝ} (ht : b ≤ 2 * t) : oldCapacity b t = 0 := by
  unfold oldCapacity
  apply max_eq_left
  linarith

theorem oldCapacity_budget (b t : ℝ) :
    1 - b + 2 * t + (9 / 2) * oldCapacity b t = max 1 (1 - b + 2 * t) := by
  by_cases ht : b ≤ 2 * t
  · rw [oldCapacity_zero ht, max_eq_right (by linarith : 1 ≤ 1 - b + 2 * t)]
    ring
  · have hc : 0 ≤ (b - 2 * t) / (9 / 2) := by linarith
    unfold oldCapacity
    rw [max_eq_right hc, max_eq_left (by linarith : 1 - b + 2 * t ≤ 1)]
    ring

theorem shiftReserve_unclipped_slope {b t1 t2 : ℝ}
    (h1 : 2 * t1 ≤ b) (h2 : 2 * t2 ≤ b) :
    shiftReserve b t2 - shiftReserve b t1 = (7 / 18) * (t2 - t1) := by
  rw [shiftReserve_unclipped h1, shiftReserve_unclipped h2]
  ring

theorem shiftReserve_clipped_slope {b t1 t2 : ℝ}
    (h1 : b ≤ 2 * t1) (h2 : b ≤ 2 * t2) :
    shiftReserve b t2 - shiftReserve b t1 = (1 / 2) * (t2 - t1) := by
  rw [shiftReserve_clipped h1, shiftReserve_clipped h2]
  ring

theorem large_shift_reserve {b t : ℝ} (hb : b ≤ 4 / 25) (ht : t0 ≤ t) :
    5747/408960000 ≤ shiftReserve b t := by
  by_cases hclip : b ≤ 2 * t
  · rw [shiftReserve_clipped hclip]
    norm_num [B, lambda, t0] at *
    linarith
  · have hu : 2 * t ≤ b := le_of_lt (lt_of_not_ge hclip)
    rw [shiftReserve_unclipped hu]
    norm_num [B, lambda, t0] at *
    linarith

theorem large_shift_paid {b t q delta : ℝ}
    (hb : b ≤ 4 / 25) (ht : t0 ≤ t) (hq0 : 0 ≤ q)
    (hq : q ≤ delta / 2) (hd : 0 ≤ delta) :
    (q / 2) * ((b - (1 - B)) / lambda - oldCapacity b t) ≤ delta * t / 2 := by
  let loss := (b - (1 - B)) / lambda - oldCapacity b t
  have hreserve := large_shift_reserve hb ht
  change 5747/408960000 ≤ t / 2 - (1 / 4) * loss at hreserve
  have hloss : loss ≤ 2 * t := by linarith
  have htp : 0 ≤ t := by norm_num [t0] at ht; linarith
  change (q / 2) * loss ≤ delta * t / 2
  by_cases hnonneg : 0 ≤ loss
  · have hqmul := mul_le_mul_of_nonneg_right hq hnonneg
    have hdmul := mul_le_mul_of_nonneg_left hloss hd
    nlinarith
  · have hleft : q * loss ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 (le_of_not_ge hnonneg)
    have hright := mul_nonneg hd htp
    nlinarith

end

end Cycle63.Physical
end

/- Original module: Candidate.Cycle63.Numerator.Capacity.Schedule. -/
section

namespace Cycle63.Numerator.Capacity

open Cycle63.Arithmetic

noncomputable section

def zeroCapacity (d : ℝ) : ℝ := Physical.affineCapacity d 0

def scheduledCapacity (d v : ℝ) : ℝ :=
  if v ≤ 2*t0 then Physical.affineCapacity d (v/2)
  else Physical.oldCapacity (Physical.shiftBase d) (v/2)

def dampingRate : ℝ := 1/1000

theorem dampingRate_pos : 0 < dampingRate := by norm_num [dampingRate]

theorem zeroCapacity_eq_shiftBase (d : ℝ) :
    zeroCapacity d = (Physical.shiftBase d-(1-B))/lambda := by
  unfold zeroCapacity Physical.affineCapacity Physical.plainScale Physical.shiftBase
  ring

theorem scaled_zeroCapacity {d : ℝ} (hd : d ≠ 0) :
    d*zeroCapacity d = (2*y-(2-B)*d)/lambda :=
  Physical.scaled_capacity_zero hd

theorem scheduledCapacity_le_supply {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) :
    scheduledCapacity d v ≤ ell/d := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hcap := Physical.capacity_supply hd
      (show 0 ≤ v/2 ∧ v/2 ≤ t0 by constructor <;> linarith)
    apply (le_div_iff₀ (Physical.physical_d_pos hd.1)).mpr
    nlinarith
  · have hb := (Physical.shiftBase_bounds hd).2.2
    have hcap : Physical.oldCapacity (Physical.shiftBase d) (v/2) ≤ 8/225 := by
      unfold Physical.oldCapacity
      apply max_le
      · norm_num
      · linarith
    have hsupply := Physical.positive_supply hd
    linarith

theorem scheduledCapacity_nonneg {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) : 0 ≤ scheduledCapacity d v := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hz := Physical.affineCapacity_interior hd
      (show 0 ≤ v/2 ∧ v/2 ≤ t0 by constructor <;> linarith)
    linarith [hz.1]
  · exact Physical.oldCapacity_nonneg _ _

theorem scheduled_small_budget {d v : ℝ} (hsmall : v ≤ 2*t0) :
    2*Physical.plainScale d (v/2)+lambda*scheduledCapacity d v = B := by
  rw [scheduledCapacity, ite_eq_left hsmall]
  exact Physical.affineCapacity_budget d (v/2)

theorem scheduled_large_budget {d v : ℝ} (hlarge : 2*t0 < v) :
    1-Physical.shiftBase d+v+(9/2)*scheduledCapacity d v =
      max 1 (1-Physical.shiftBase d+v) := by
  rw [scheduledCapacity, ite_eq_right (not_le.mpr hlarge)]
  have hh := Physical.oldCapacity_budget (Physical.shiftBase d) (v/2)
  rwa [show 2*(v/2) = v by ring] at hh

theorem large_shift_proportional_reserve {b t : ℝ}
    (hb : b ≤ 4/25) (ht : t0 ≤ t) : t/500 ≤ Physical.shiftReserve b t := by
  by_cases hclip : b ≤ 2*t
  · rw [Physical.shiftReserve_clipped hclip]
    norm_num [B, lambda, t0] at *
    linarith
  · have hu : 2*t ≤ b := le_of_lt (lt_of_not_ge hclip)
    rw [Physical.shiftReserve_unclipped hu]
    norm_num [B, lambda, t0] at *
    linarith

theorem scheduled_capacity_damping {d v q delta : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hdelta : 0 ≤ delta) :
    q*zeroCapacity d/2+dampingRate*delta*v ≤
      delta*v/4+q*scheduledCapacity d v/2 := by
  by_cases hsmall : v ≤ 2*t0
  · rw [scheduledCapacity, ite_eq_left hsmall]
    have hid := Physical.affineCapacity_shift d (v/2)
    change zeroCapacity d-Physical.affineCapacity d (v/2) = 2*(v/2)/lambda at hid
    have hm := mul_nonneg (sub_nonneg.mpr hqdelta) hv
    have hnonneg := mul_nonneg hdelta hv
    norm_num [lambda, dampingRate] at hid ⊢
    nlinarith
  · rw [scheduledCapacity, ite_eq_right hsmall]
    have ht : t0 ≤ v/2 := by linarith [lt_of_not_ge hsmall]
    have hb : Physical.shiftBase d ≤ 4/25 := (Physical.shiftBase_bounds hd).2.2.le
    have hreserve := large_shift_proportional_reserve hb ht
    rw [Physical.shiftReserve, ← zeroCapacity_eq_shiftBase d] at hreserve
    let loss := zeroCapacity d-Physical.oldCapacity (Physical.shiftBase d) (v/2)
    have ht0 : 0 ≤ v/2 := by linarith
    change (v/2)/500 ≤ (v/2)/2-(1/4)*loss at hreserve
    change q*zeroCapacity d/2+dampingRate*delta*v ≤
      delta*v/4+q*Physical.oldCapacity (Physical.shiftBase d) (v/2)/2
    by_cases hloss : 0 ≤ loss
    · have hqmul := mul_le_mul_of_nonneg_right hqdelta hloss
      have hdmul := mul_le_mul_of_nonneg_left hreserve hdelta
      dsimp only [loss] at hqmul hdmul
      norm_num [dampingRate] at *
      nlinarith
    · have hqmul := mul_nonpos_of_nonneg_of_nonpos hq (le_of_not_ge hloss)
      have hdmul := mul_nonneg hdelta hv
      dsimp only [loss] at hqmul
      norm_num [dampingRate]
      nlinarith

end
end Cycle63.Numerator.Capacity
end
