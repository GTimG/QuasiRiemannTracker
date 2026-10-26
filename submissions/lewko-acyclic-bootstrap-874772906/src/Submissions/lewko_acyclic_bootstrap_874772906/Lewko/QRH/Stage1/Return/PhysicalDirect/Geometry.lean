/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Gao Target830 physical geometry, with the literal new face,
individual plain edge 2/5 and free shift 1/400 from Ch24.5. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.PhysicalDirect.ClippedCapacityDamping
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Numerator.BoxGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

open QRH.LewkoStage1Return

namespace QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.LewkoStage1Return.GenericArithmetic
open QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect

def plainUpper : ℝ := 11/25
def widthLower : ℝ := 17/500
def widthUpper : ℝ := 1/25

theorem physicalLambda_pos : 0 < physicalLambda := by
 have hh := PhysicalSchedule.lambda_bounds.1
 linarith


def plainScale (d t : ℝ) : ℝ := 1-y/d+t
def affineCapacity (d t : ℝ) : ℝ := (physicalB-2*plainScale d t)/physicalLambda
def clippedCapacity (d t : ℝ) : ℝ := min cap (affineCapacity d t)
def shiftBase (d : ℝ) : ℝ := 2*y/d-1
def oldCapacity (b t : ℝ) : ℝ := max 0 ((b-2*t)/(9/2))
def zeroCapacity (d : ℝ) : ℝ := clippedCapacity d 0
def scheduledCapacity (d v : ℝ) : ℝ :=
 if v≤2*freeShift then clippedCapacity d (v/2) else oldCapacity (shiftBase d) (v/2)
def dampingRate : ℝ := 1/1000

theorem physical_d_pos {d : ℝ} (hd : dm ≤ d) : 0 < d := by
 have hh := PhysicalSchedule.dMinus_lower
 linarith


theorem plainScale_exact_bounds {d t : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t ∧ t ≤ freeShift) :
    1-y/dm ≤ plainScale d t ∧ plainScale d t ≤ 1-y/dp+freeShift := by
  have hy : 0 ≤ y := by linarith [Geometry.Bounds.ly_coarse.1]
  have hp := physical_d_pos hd.1
  have hhi := div_le_div_of_nonneg_left hy (show 0<dm from physical_d_pos le_rfl) hd.1
  have hlo := div_le_div_of_nonneg_left hy hp hd.2
  unfold plainScale
  constructor <;> linarith

theorem plainScale_interior {d t : ℝ}
 (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t ∧ t ≤ freeShift) :
 plainLower < plainScale d t ∧ plainScale d t < 264/625 := by
 have hn := plainScale_exact_bounds hd ht
 have hlo := PhysicalSchedule.physical_plain_lower
 have hhi := PhysicalSchedule.physical_plain_upper
 constructor <;> linarith


theorem affineCapacity_bounds {d t : ℝ}
 (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t ∧ t ≤ freeShift) :
 widthLower < affineCapacity d t := by
 have hn := (plainScale_exact_bounds hd ht).2
 have hf := (lt_div_iff₀ physicalLambda_pos).mp PhysicalSchedule.physical_width_lower
 apply (lt_div_iff₀ physicalLambda_pos).mpr
 change (17/500:ℝ)*physicalLambda < physicalB-2*plainScale d t
 linarith


theorem affineCapacity_interior {d t : ℝ}
 (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t ∧ t ≤ freeShift) :
 widthLower < affineCapacity d t := affineCapacity_bounds hd ht

theorem clippedCapacity_interior {d t : ℝ}
 (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t ∧ t ≤ freeShift) :
 widthLower < clippedCapacity d t ∧ clippedCapacity d t ≤ cap := by
 constructor
 · exact lt_min (by norm_num [widthLower,cap]) (affineCapacity_bounds hd ht)
 · exact min_le_left _ _


theorem affineCapacity_budget (d t : ℝ) :
    2 * plainScale d t + physicalLambda * affineCapacity  d t = physicalB := by
  have hp : physicalLambda ≠ 0 := ne_of_gt (physicalLambda_pos)
  unfold affineCapacity
  field_simp
  ring

theorem affineCapacity_shift (d t : ℝ) :
    affineCapacity  d 0 - affineCapacity  d t = 2 * t / physicalLambda := by
  unfold affineCapacity plainScale
  ring

theorem affine_shortening {d t n1 n2 z : ℝ}
    (h1 : n1 ≤ plainScale d t) (h2 : n2 ≤ plainScale d t)
    (hz : z ≤ affineCapacity  d t) : n1 + n2 + physicalLambda * z ≤ physicalB := by
  have hpos := physicalLambda_pos
  have hmul := mul_le_mul_of_nonneg_left hz hpos.le
  have hh := affineCapacity_budget  d t
  linarith

theorem small_slot_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 264 / 625) (h2 : n2 ≤ 264 / 625)
    (hz : z ≤ widthLower) : n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 5000 := by
  norm_num [widthLower] at hz
  linarith

theorem small_plain_shortening {n1 n2 n z : ℝ}
 (h1 : n1 ≤ plainLower) (h2 : n2 ≤ n)
 (hcone : 2*n+physicalLambda*z ≤ physicalB) (hz : z ≤ widthUpper) :
 n1+n2+(9/2)*z ≤ 1 := by
 have hl := PhysicalSchedule.lambda_bounds.2
 have hc : 0 ≤ 9/2-physicalLambda/2 := by linarith
 have hz' : z ≤ cap := by simpa [widthUpper,cap] using hz
 have hm := mul_le_mul_of_nonneg_left hz' hc
 have hs := PhysicalSchedule.small_plain_shortening
 nlinarith


theorem positive_supply {d : ℝ} (hd : dm ≤ d ∧ d ≤ dp) :
 1/5 < ell/d := by
 have hh := div_le_div_of_nonneg_left Geometry.ell_pos.le (physical_d_pos hd.1) hd.2
 exact PhysicalSchedule.prime_supply.trans_le hh


theorem shiftBase_bounds {d : ℝ} (hd : dm ≤ d ∧ d ≤ dp) :
 0 ≤ shiftBase d ∧ shiftBase d ≤ 9/50 := by
 have hy : 0 ≤ y := by linarith [Geometry.Bounds.ly_coarse.1]
 have hp := physical_d_pos hd.1
 have hhi := div_le_div_of_nonneg_left hy (physical_d_pos le_rfl) hd.1
 have hdp : dp < 2*y := by
  change Geometry.h+1/10000000000 < 2*Geometry.y
  linarith [Geometry.Bounds.h_interval.2,Geometry.Bounds.ly_coarse.1]
 have hr : (1/2:ℝ) ≤ y/d := by
  apply (le_div_iff₀ hp).mpr
  linarith [hd.2]
 have hb := PhysicalSchedule.shift_bound
 unfold shiftBase
 rw [mul_div_assoc] at hb ⊢
 constructor <;> linarith


theorem scheduledCapacity_nonneg {d v : ℝ}
 (hd : dm ≤ d ∧ d ≤ dp) (hv : 0 ≤ v) : 0 ≤ scheduledCapacity d v := by
 unfold scheduledCapacity
 split_ifs with hs
 · have hh := (clippedCapacity_interior hd
    (show 0 ≤ v/2 ∧ v/2 ≤ freeShift by constructor <;> linarith)).1
   have hw : (0:ℝ) ≤ widthLower := by norm_num [widthLower]
   linarith
 · exact le_max_left _ _


theorem scheduledCapacity_le_supply {d v : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (hv : 0 ≤ v) :
    scheduledCapacity  d v ≤ ell / d := by
  have hs := positive_supply hd
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hh : clippedCapacity d (v/2) ≤ cap := min_le_left _ _
    have hc : cap < 1 / 5 := by norm_num [cap]
    exact hh.trans (hc.le.trans hs.le)
  · have hb := (shiftBase_bounds hd).2
    have hh : oldCapacity (shiftBase d) (v / 2) ≤ 1 / 25 := by
      unfold oldCapacity
      apply max_le
      · norm_num
      · linarith
    linarith

theorem zeroCapacity_eq_kernel (d : ℝ) :
    zeroCapacity  d = ClippedCapacityDamping.baseCapacity
      physicalLambda cap (1 - physicalB) (shiftBase d) := by
  unfold zeroCapacity clippedCapacity affineCapacity plainScale shiftBase
    ClippedCapacityDamping.baseCapacity
  congr 1
  ring

theorem scheduledCapacity_eq_kernel (d v : ℝ) :
    scheduledCapacity  d v = ClippedCapacityDamping.scheduledAt
      physicalLambda cap (1 - physicalB) (shiftBase d) freeShift (v / 2) := by
  unfold scheduledCapacity ClippedCapacityDamping.scheduledAt
  have hi : v ≤ 2 * freeShift ↔ v / 2 ≤ freeShift := by
    constructor <;> intro hh <;> linarith
  by_cases hs : v ≤ 2 * freeShift
  · rw [ite_eq_left hs, ite_eq_left (hi.mp hs)]
    unfold clippedCapacity affineCapacity plainScale shiftBase ClippedCapacityDamping.shiftedCapacity
    congr 1
    ring
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hi.mpr h))]
    rfl

theorem scheduled_capacity_damping {d v a delta : ℝ}
    (_hd : dm ≤ d ∧ d ≤ dp) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (had : a ≤ delta / 2) (hdelta : 0 ≤ delta) :
    a * zeroCapacity  d / 2 + dampingRate * delta * v ≤
      delta * v / 4 + a * scheduledCapacity  d v / 2 := by
  have hl : 2 ≤ physicalLambda := PhysicalSchedule.lambda_bounds.1
  have hlarge : ∀ u : ℝ, freeShift ≤ u → u / 500 ≤
      ClippedCapacityDamping.reserve physicalLambda cap (1 - physicalB) (shiftBase d) u := by
    intro u hu
    have hg := ClippedCapacityDamping.global_clipped_reserve physicalLambda cap (1-physicalB)
      (shiftBase d) u physicalLambda_pos PhysicalSchedule.lambda_bounds.2
    have hr := PhysicalSchedule.large_shift_reserve
    have hi : 0 ≤ (7/18-1/500)*(u-freeShift) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hu)
    linarith
  have hh := ClippedCapacityDamping.scheduled_amplitude_damping
    physicalLambda cap (1 - physicalB) (shiftBase d) freeShift (v / 2) a delta
    hl (by linarith) ha had hdelta hlarge
  rw [← zeroCapacity_eq_kernel  d, ← scheduledCapacity_eq_kernel  d v] at hh
  dsimp [dampingRate]
  convert hh using 1 <;> ring

theorem scaled_zeroCapacity {d : ℝ} (hd : 0 < d) :
    d * zeroCapacity  d =
      min (cap * d) ((2 * y - (2 - physicalB) * d) / physicalLambda) := by
  unfold zeroCapacity clippedCapacity
  rw [mul_min_of_nonneg _ _ hd.le]
  congr 1
  · ring
  · unfold affineCapacity plainScale
    field_simp
    ring

theorem physical_y_range {d : ℝ} (hd : dm ≤ d ∧ d ≤ dp) :
    1 / 2 ≤ y / d ∧ y / d < 1 := by
  have hb := (shiftBase_bounds hd).1
  have hp := physical_d_pos hd.1
  constructor
  · unfold shiftBase at hb
    rw [mul_div_assoc] at hb
    linarith
  · apply (div_lt_one hp).mpr
    have hh : y < dm := PhysicalSchedule.y_before_switch
    exact hh.trans_le hd.1

theorem coefficient_box_geometry {d xi ann : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (hxi : 0 < xi) (_hann : 0 ≤ ann)
    (hsmall : 2 * xi + ann ≤ 1 / 2) (j : ℕ)
    (hj : j ∈ Finset.range (Cycle25.Numerator.coefficientBoxCount xi + 1)) :
    0 ≤ 1 - y / d + (j : ℝ) * xi + xi ∧
      (1 - y / d + (j : ℝ) * xi + xi) + ann ≤ 2 := by
  have hy := physical_y_range hd
  have hv := Cycle25.Numerator.coefficient_box_index_range xi hxi j hj
  constructor <;> linarith

theorem scheduled_capacity_or_empty {α : Type*}
    (T : Finset α) (width : T → ℝ) {d t kap : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t) (hkap : kap ≤ 3 / 4)
    (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity  d (2 * t)) :
    (∃ d' t' : ℝ, dm ≤ d' ∧ d' ≤ dp ∧ 0 ≤ t' ∧ t' ≤ freeShift ∧
      plainScale d t = plainScale d' t' ∧ (∑ i, width i) ≤ clippedCapacity d' t') ∨
      (2 * plainScale d t + 6 * kap * (∑ i, width i) ≤ 1 ∨ T = ∅) := by
  have hsum : 0 ≤ ∑ i, width i := Finset.sum_nonneg (fun i _ => (hw i).le)
  by_cases hsmall : t ≤ freeShift
  · left
    refine ⟨d, t, hd.1, hd.2, ht, hsmall, rfl, ?_⟩
    simpa [scheduledCapacity, show 2 * t ≤ 2 * freeShift by linarith] using hselected
  · right
    have hselected' : (∑ i, width i) ≤ oldCapacity (shiftBase d) t := by
      simpa [scheduledCapacity, show ¬ 2 * t ≤ 2 * freeShift by linarith] using hselected
    by_cases hraw : 0 ≤ (shiftBase d - 2 * t) / (9 / 2)
    · left
      have hs : (∑ i, width i) ≤ (shiftBase d - 2 * t) / (9 / 2) := by
        simpa [oldCapacity, max_eq_right hraw] using hselected'
      have hbudget : 2 * plainScale d t + (9 / 2) * (∑ i, width i) ≤ 1 := by
        unfold plainScale shiftBase at *
        rw [mul_div_assoc] at hs
        linarith
      nlinarith
    · right
      have hs : (∑ i, width i) ≤ 0 := by
        simpa [oldCapacity, max_eq_left (le_of_not_ge hraw)] using hselected'
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := Finset.single_le_sum (fun (j : T) (_ : j ∈ Finset.univ) => (hw j).le)
        (Finset.mem_univ (⟨i, hi⟩ : T))
      linarith [hw ⟨i, hi⟩]

end QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect

#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.scheduled_capacity_damping
#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.scaled_zeroCapacity
#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.scheduled_capacity_or_empty
