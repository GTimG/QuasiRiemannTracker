/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle62.Numerator.Scalar.Exponent
import Candidate.Cycle62.Numerator.Capacity.Schedule

noncomputable section
namespace Cycle62.Numerator.Scalar
open Cycle62.Arithmetic Cycle62.Arithmetic.Bernstein

theorem zeroCapacity_binding {d : ℝ} (hd : d ≠ 0) :
    d*Capacity.zeroCapacity d = newCapacity d := Capacity.scaled_zeroCapacity hd

def scheduledBinExponent (kap d delta p v xi : ℝ) : ℝ :=
  numeratorExponent kap d (d*Capacity.scheduledCapacity d (v+xi)) delta p-
    d*delta*v/4

/-- Both the affine small-shift schedule and the clipped large-shift schedule
pay the loss from the zero-shift capacity, including an explicit damping gain. -/
theorem scheduled_bin_damping {kap d delta p v xi : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p ∧ p ≤ 1/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) :
    scheduledBinExponent kap d delta p v xi ≤
      numeratorExponent kap d (newCapacity d) delta p+d*delta*xi/4-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hdpos := Physical.physical_d_pos hd.1
  have hq : 0 ≤ delta*p := mul_nonneg hdelta hp.1
  have hq1 : delta*p ≤ delta/2 := by nlinarith [mul_le_mul_of_nonneg_left hp.2 hdelta]
  have hh := Capacity.scheduled_capacity_damping hd (add_nonneg hv hxi) hq hq1 hdelta
  have hm := mul_le_mul_of_nonneg_left hh hdpos.le
  rw [←zeroCapacity_binding hdpos.ne']
  unfold scheduledBinExponent numeratorExponent
  nlinarith only [hm]

theorem scheduled_small_capacity {d v : ℝ} (hv : v ≤ 2*t0) :
    Capacity.scheduledCapacity d v = Physical.affineCapacity d (v/2) := by
  simp only [Capacity.scheduledCapacity,ite_eq_left hv]

theorem scheduled_large_capacity {d v : ℝ} (hv : 2*t0 < v) :
    Capacity.scheduledCapacity d v = Physical.oldCapacity (Physical.shiftBase d) (v/2) := by
  simp only [Capacity.scheduledCapacity,ite_eq_right (not_le.mpr hv)]

theorem scheduled_clipped_capacity {d v : ℝ} (hv : 2*t0 < v)
    (hclip : Physical.shiftBase d ≤ v) : Capacity.scheduledCapacity d v = 0 := by
  rw [scheduled_large_capacity hv]
  exact Physical.oldCapacity_zero (by linarith)

theorem scheduled_kernel_bound {kap d delta p v xi e : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p ∧ p ≤ 1/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) :
    scheduledBinExponent kap d delta p v xi+kernelExponent ((1+delta)/2) e ≤
      newExponentAt kap d delta p+Assembly.signalShift+16*e+d*delta*xi/4-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hh := scheduled_bin_damping (kap:=kap) hd hdelta hp hv hxi
  have hi := numerator_kernel_exponent kap d (newCapacity d) delta p e
  unfold newExponentAt
  linarith only [hh,hi]

end Cycle62.Numerator.Scalar
