/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: Lemma D, the physical face applied at every shift.
Fork of Collet's PhysicalDirect/Geometry.lean (Record1252270103Return, Apache-2.0; adapted from Gao
Target830 physical geometry), re-elaborated in QRH.RepeatedMarks.Return.

Collet applies the physical face on a window: plain lengths in `[2/5,11/25]`, slot widths in
`[17/500,1/25]` and shifts `t ≤ 1/400`, and uses the natural moment (coefficient `9/2`) for larger
shifts. The face is a global source theorem (plain floor `0`, width floor `0`), so here the shifted
configuration `(n₀+t,n₀+t,z)` is admitted for every shift `t ≥ 0` as long as `z` lies below the
clipped affine capacity of the face, and the capacity is `0` once the shifted plain length leaves
the face. The width lost by a shift is at most `2t/Λ` (`small_clip_loss_le`), which the shift pays
(`small_shift_reserve`); no window, free shift or large-shift reserve is needed. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.ClippedCapacityDamping
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

open QRH.Record1252270103Return

namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic
open Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect

theorem physicalLambda_pos : 0 < physicalLambda := by
 have hh := PhysicalSchedule.lambda_bounds.1
 linarith

def plainScale (d t : ℝ) : ℝ := 1-y/d+t
def affineCapacity (d t : ℝ) : ℝ := (physicalB-2*plainScale d t)/physicalLambda
def clippedCapacity (d t : ℝ) : ℝ := min cap (affineCapacity d t)
def shiftBase (d : ℝ) : ℝ := 2*y/d-1
def zeroCapacity (d : ℝ) : ℝ := clippedCapacity d 0
/-- Lemma D: the capacity at every shift is the clipped affine capacity of the global face. -/
def scheduledCapacity (d v : ℝ) : ℝ := max 0 (clippedCapacity d (v/2))
def dampingRate : ℝ := 1/1000

theorem physical_d_pos {d : ℝ} (hd : dm ≤ d) : 0 < d := by
 have hh := PhysicalSchedule.dMinus_lower
 linarith

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

/-- A nonpositive plain length leaves the natural budget: the global face has plain floor `0`. -/
theorem small_plain_shortening {n1 n2 n z : ℝ}
 (h1 : n1 ≤ 0) (h2 : n2 ≤ n)
 (hcone : 2*n+physicalLambda*z ≤ physicalB) (hz : z ≤ cap) :
 n1+n2+(9/2)*z ≤ 1 := by
 have hl := PhysicalSchedule.lambda_bounds.2
 have hc : 0 ≤ 9/2-physicalLambda/2 := by linarith
 have hm := mul_le_mul_of_nonneg_left hz hc
 have hs := PhysicalSchedule.small_plain_global
 nlinarith

theorem positive_supply {d : ℝ} (hd : dm ≤ d ∧ d ≤ dp) :
 1/5 < ell/d := by
 have hh := div_le_div_of_nonneg_left Geometry.ell_pos.le (physical_d_pos hd.1) hd.2
 exact PhysicalSchedule.prime_supply.trans_le hh

theorem shiftBase_nonneg {d : ℝ} (hd : dm ≤ d ∧ d ≤ dp) : 0 ≤ shiftBase d := by
 have hp := physical_d_pos hd.1
 have hdp : dp < 2*y := by
  change Geometry.h+1/10000000000 < 2*Geometry.y
  linarith [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.h_interval.2,Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.ly_coarse.1]
 have hr : (1:ℝ) ≤ 2*y/d := by
  apply (le_div_iff₀ hp).mpr
  linarith [hd.2]
 unfold shiftBase
 linarith

theorem scheduledCapacity_nonneg {d v : ℝ}
 (_hd : dm ≤ d ∧ d ≤ dp) (_hv : 0 ≤ v) : 0 ≤ scheduledCapacity d v :=
 le_max_left _ _

theorem scheduledCapacity_le_supply {d v : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (_hv : 0 ≤ v) :
    scheduledCapacity  d v ≤ ell / d := by
  have hs := positive_supply hd
  have hc : cap < 1 / 5 := PhysicalSchedule.cap_lt_fifth
  unfold scheduledCapacity
  apply max_le (by linarith)
  exact (min_le_left _ _).trans (hc.le.trans hs.le)

theorem zeroCapacity_eq_kernel (d : ℝ) :
    zeroCapacity  d = ClippedCapacityDamping.baseCapacity
      physicalLambda cap (1 - physicalB) (shiftBase d) := by
  unfold zeroCapacity clippedCapacity affineCapacity plainScale shiftBase
    ClippedCapacityDamping.baseCapacity
  congr 1
  ring

theorem clippedCapacity_eq_kernel (d t : ℝ) :
    clippedCapacity d t = ClippedCapacityDamping.shiftedCapacity
      physicalLambda cap (1 - physicalB) (shiftBase d) t := by
  unfold clippedCapacity affineCapacity plainScale shiftBase ClippedCapacityDamping.shiftedCapacity
  congr 1
  ring

/-- Lemma D, payment: the width lost by a shift is paid by the shift, for every shift. -/
theorem scheduled_capacity_damping {d v a delta : ℝ}
    (_hd : dm ≤ d ∧ d ≤ dp) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (had : a ≤ delta / 2) (hdelta : 0 ≤ delta) :
    a * zeroCapacity  d / 2 + dampingRate * delta * v ≤
      delta * v / 4 + a * scheduledCapacity  d v / 2 := by
  have hl : 2 ≤ physicalLambda := PhysicalSchedule.lambda_bounds.1
  have hr := ClippedCapacityDamping.small_shift_reserve physicalLambda cap (1 - physicalB)
    (shiftBase d) (v / 2) hl (by linarith)
  have hh := ClippedCapacityDamping.amplitude_of_reserve _ _ (v / 2) a delta (by linarith) ha had
    hdelta hr
  rw [← zeroCapacity_eq_kernel d, ← clippedCapacity_eq_kernel d (v / 2)] at hh
  have hmax : a * clippedCapacity d (v / 2) ≤ a * scheduledCapacity d v :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) ha
  dsimp [dampingRate]
  have e1 : delta * (2 * (v / 2)) = delta * v := by ring
  rw [e1] at hh
  linarith

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
  have hb := shiftBase_nonneg hd
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

/-- Lemma D, admissibility: a nonempty selection below the scheduled capacity lies in the global
physical face at the shifted plain length. -/
theorem scheduled_capacity_or_empty {α : Type*}
    (T : Finset α) (width : T → ℝ) {d t kap : ℝ}
    (hd : dm ≤ d ∧ d ≤ dp) (ht : 0 ≤ t) (_hkap : kap ≤ 3 / 4)
    (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity  d (2 * t)) :
    (∃ d' t' : ℝ, dm ≤ d' ∧ d' ≤ dp ∧ 0 ≤ t' ∧
      plainScale d t = plainScale d' t' ∧ (∑ i, width i) ≤ clippedCapacity d' t') ∨
      (2 * plainScale d t + 6 * kap * (∑ i, width i) ≤ 1 ∨ T = ∅) := by
  by_cases hT : T = ∅
  · exact Or.inr (Or.inr hT)
  · left
    refine ⟨d, t, hd.1, hd.2, ht, rfl, ?_⟩
    obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hne : (Finset.univ : Finset T).Nonempty := ⟨⟨i0, hi0⟩, Finset.mem_univ _⟩
    have hpos : 0 < ∑ i, width i := Finset.sum_pos (fun i _ => hw i) hne
    have h2 : 2 * t / 2 = t := by ring
    have hsel : (∑ i, width i) ≤ max 0 (clippedCapacity d t) := by
      simpa only [scheduledCapacity, h2] using hselected
    rcases le_total (clippedCapacity d t) 0 with hc | hc
    · rw [max_eq_left hc] at hsel
      linarith
    · rwa [max_eq_right hc] at hsel

end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
