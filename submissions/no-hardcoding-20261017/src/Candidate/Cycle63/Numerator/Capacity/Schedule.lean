import Candidate.Cycle63.Physical.Capacity

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
  · have hb := Physical.shiftBase_bounds hd
    have hcap : Physical.oldCapacity (Physical.shiftBase d) (v/2) ≤ 2/45 := by
      unfold Physical.oldCapacity
      apply max_le
      · norm_num
      · rw [div_le_iff₀ (by norm_num)]
        linarith [hb.2.1, hb.2.2, show 0 ≤ v from hv]
    have hsupply := Physical.positive_supply hd
    linarith

theorem scheduledCapacity_nonneg {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) : 0 ≤ scheduledCapacity d v := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hz := Physical.affineCapacity_interior hd
      (show 0 ≤ v/2 ∧ v/2 ≤ t0 by constructor <;> linarith)
    linarith [hz.1, Cycle63.Optimization.slotFloor_pos]
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

theorem scheduled_capacity_damping {d v q delta : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hdelta : 0 ≤ delta) :
    q*zeroCapacity d/2+dampingRate*delta*v ≤
      delta*v/4+q*scheduledCapacity d v/2 := by
  by_cases hsmall : v ≤ 2*t0
  · rw [scheduledCapacity, ite_eq_left hsmall]
    have hid := Physical.affineCapacity_shift d (v/2)
    change zeroCapacity d-Physical.affineCapacity d (v/2) = 2*(v/2)/lambda at hid
    have hl := lambda_bounds'
    have hlam : 0 < lambda := by linarith [hl.1]
    have hw0 : 0 ≤ v/lambda := div_nonneg hv hlam.le
    have hw1 : v/lambda ≤ v/(39/10) := div_le_div_of_nonneg_left hv (by norm_num) hl.1.le
    have hzc : zeroCapacity d = Physical.affineCapacity d (v/2) + v/lambda := by
      rw [show v/lambda = 2*(v/2)/lambda by ring, ← hid]; ring
    rw [hzc]
    have hq2 := mul_le_mul_of_nonneg_right hqdelta hw0
    have hdw := mul_le_mul_of_nonneg_left hw1 hdelta
    have hnonneg := mul_nonneg hdelta hv
    unfold dampingRate
    nlinarith
  · rw [scheduledCapacity, ite_eq_right hsmall]
    have ht : t0 ≤ v/2 := by linarith [lt_of_not_ge hsmall]
    have hb : Physical.shiftBase d ≤ Physical.shiftBase dMinus := (Physical.shiftBase_bounds hd).2.1
    have hreserve := Physical.large_shift_reserve hb ht
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
