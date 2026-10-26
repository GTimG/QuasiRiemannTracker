/- Repeated marks: fork of Collet's generic return module PhysicalDirect.ClippedCapacityDamping (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Zhongpai Gao/Hailey Collet clipped capacity argument, Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule

/-! Global clipped-capacity and scheduled amplitude damping.
This is a scalar component only: no analytic moment, source provider,
profile transport or zero-free endpoint is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.ClippedCapacityDamping
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section

def oldCapacity (b t : ℝ) : ℝ := max 0 ((b - 2 * t) / (9 / 2))

def baseCapacity (lam c k b : ℝ) : ℝ := min c ((b - k) / lam)

def shiftedCapacity (lam c k b t : ℝ) : ℝ :=
  min c ((b - k - 2 * t) / lam)

def reserve (lam c k b t : ℝ) : ℝ :=
  t / 2 - (baseCapacity lam c k b - oldCapacity b t) / 4

theorem clipped_base_minimum (lam c k b : ℝ)
    (hlam : 0 < lam) (hlamhi : lam ≤ 9 / 2) :
    k / 18 + (lam / 18 - 1 / 4) * c ≤
      b / 18 - baseCapacity lam c k b / 4 := by
  by_cases hbc : k + lam * c ≤ b
  · have hcap : c ≤ (b - k) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith
    rw [baseCapacity, min_eq_left hcap]
    nlinarith
  · have hbc' : b ≤ k + lam * c := le_of_not_ge hbc
    have hcap : (b - k) / lam ≤ c := by
      apply (div_le_iff₀ hlam).mpr
      nlinarith
    rw [baseCapacity, min_eq_right hcap]
    have hp : 0 ≤ (9 - 2 * lam) * (k + lam * c - b) :=
      mul_nonneg (by linarith) (by linarith)
    have hid : lam * ((b / 18 - ((b - k) / lam) / 4) -
        (k / 18 + (lam / 18 - 1 / 4) * c)) =
        ((9 - 2 * lam) * (k + lam * c - b)) / 36 := by
      field_simp [ne_of_gt hlam]
      ring
    have hn : 0 ≤ lam * ((b / 18 - ((b - k) / lam) / 4) -
        (k / 18 + (lam / 18 - 1 / 4) * c)) := by
      rw [hid]
      positivity
    nlinarith

/-- The global inequality is valid for all real b and t, across the zero
crossing of the old capacity. No upper bound such as b <= .16 occurs. -/
theorem global_clipped_reserve (lam c k b t : ℝ)
    (hlam : 0 < lam) (hlamhi : lam ≤ 9 / 2) :
    7 * t / 18 + k / 18 + (lam / 18 - 1 / 4) * c ≤
      reserve lam c k b t := by
  have hco : (b - 2 * t) / (9 / 2) ≤ oldCapacity b t :=
    le_max_right _ _
  have hmin := clipped_base_minimum lam c k b hlam hlamhi
  dsimp [reserve]
  linarith

theorem min_difference_le (c u v : ℝ) (hvu : v ≤ u) :
    min c u - min c v ≤ u - v := by
  by_cases hcv : c ≤ v
  · rw [min_eq_left (hcv.trans hvu), min_eq_left hcv]
    linarith
  · rw [min_eq_right (le_of_not_ge hcv)]
    exact sub_le_sub_right (min_le_right c u) v

/-- Clipping cannot increase the capacity lost by a nonnegative shift. -/
theorem small_clip_loss_le (lam c k b t : ℝ)
    (hlam : 0 < lam) (ht : 0 ≤ t) :
    baseCapacity lam c k b - shiftedCapacity lam c k b t ≤ 2 * t / lam := by
  have hs : (b - k - 2 * t) / lam ≤ (b - k) / lam := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hlam)
    linarith
  calc
    _ ≤ (b - k) / lam - (b - k - 2 * t) / lam :=
      min_difference_le c _ _ hs
    _ = 2 * t / lam := by ring

def scheduledAt (lam c k b t0 t : ℝ) : ℝ :=
  if t ≤ t0 then shiftedCapacity lam c k b t else oldCapacity b t

theorem small_shift_reserve (lam c k b t : ℝ)
    (hlamlo : 2 ≤ lam) (ht : 0 ≤ t) :
    t / 500 ≤ t / 2 -
      (baseCapacity lam c k b - shiftedCapacity lam c k b t) / 4 := by
  have hlam : 0 < lam := by linarith
  have hloss := small_clip_loss_le lam c k b t hlam ht
  have hdiv : 2 * t / lam ≤ t := by
    apply (div_le_iff₀ hlam).mpr
    nlinarith
  linarith

theorem amplitude_of_reserve (C0 C t a delta : ℝ)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (had : a ≤ delta / 2) (hd : 0 ≤ delta)
    (hr : t / 500 ≤ t / 2 - (C0 - C) / 4) :
    a * C0 / 2 + delta * (2 * t) / 1000 ≤
      delta * (2 * t) / 4 + a * C / 2 := by
  by_cases hL : 0 ≤ C0 - C
  · have hmul := mul_le_mul_of_nonneg_right had hL
    have hres := mul_le_mul_of_nonneg_left hr hd
    nlinarith
  · have hmul := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hL)
    have hdt := mul_nonneg hd ht
    nlinarith

/-- Scalar interface used by the genuine weighted coefficient-bin consumer.
The analytic moment at the scheduled capacity remains a separate input. -/
theorem scheduled_amplitude_damping (lam c k b t0 t a delta : ℝ)
    (hlamlo : 2 ≤ lam) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (had : a ≤ delta / 2) (hd : 0 ≤ delta)
    (hlarge : ∀ u : ℝ, t0 ≤ u → u / 500 ≤ reserve lam c k b u) :
    a * baseCapacity lam c k b / 2 + delta * (2 * t) / 1000 ≤
      delta * (2 * t) / 4 + a * scheduledAt lam c k b t0 t / 2 := by
  apply amplitude_of_reserve _ _ t a delta ht ha had hd
  by_cases hsmall : t ≤ t0
  · rw [scheduledAt, ite_eq_left hsmall]
    exact small_shift_reserve lam c k b t hlamlo ht
  · rw [scheduledAt, ite_eq_right hsmall]
    exact hlarge t (le_of_not_ge hsmall)

end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.ClippedCapacityDamping
