import Candidate.Cycle63.Arithmetic.LocalReserves
import Candidate.Cycle63.Arithmetic.Constants
import Candidate.Cycle63.Arithmetic.FirstLevel

namespace Cycle63.Physical
noncomputable section
open Cycle63.AffineLedger

/-- The supported-width allowance is nonnegative, but the actual width
difference may be negative. This is the paid-deletion inequality (2.16). -/
theorem paid_deletion_bound {d δ F r : ℝ} (hd : d ≤ δ) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r ∧ r ≤ 1) : d+r*max (F-d) 0 ≤ δ+r*max F 0 := by
  by_cases hFd : d ≤ F
  · rw [max_eq_left (sub_nonneg.mpr hFd)]
    have h₁ := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1-r by linarith [hr.2])
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left F 0) hr.1
    nlinarith [mul_nonneg hr.1 hδ]
  · rw [max_eq_right (show F-d ≤ 0 by linarith)]
    nlinarith [mul_nonneg hr.1 (le_max_right F 0)]

variable [Cycle63.AffineLedger] in
/-- After the actual width defect and greedy deletion have been paid, the
six-amplifier defect still leaves the strict low reserve. -/
theorem low_paid_excess_bound [Cycle63.AffineLedger.DeletesIntoOldRegion] {b M d δ F padding : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hd : d ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (hF : F ≤ M*g b+6*(M*amp b)+padding) :
    d+lowRate*max (F-d) 0-δ-M*amp b ≤
      -M*(Cycle63.AffineLedger.lowReserve)+lowRate*padding := by
  have hg := g_pos hb
  have ha := amp_pos hb
  have hcap : 0 ≤ M*g b+6*(M*amp b)+padding := by positivity
  have hmax := max_le hF hcap
  have hr := lowRate_mem
  have hpaid := paid_deletion_bound (F := F) hd hδ ⟨hr.1.le, hr.2⟩
  have hprod := mul_le_mul_of_nonneg_left hmax hr.1.le
  have hid : M*amp b-lowRate*(M*g b+6*(M*amp b)) = M*(Cycle63.AffineLedger.lowReserve) := by
    have h := low_reserve_old b
    linear_combination M * h
  linarith

variable [Cycle63.AffineLedger] in
theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hBc : 0 ≤ Bc) :
    A-M-min c d-Bc+5*a ≤ -M*zeroReserve := by
  have hreserve := mul_le_mul_of_nonneg_left (second_zero_reserve hb) hM
  have hmin : 0 ≤ min c d := le_min hc hd
  nlinarith

end
end Cycle63.Physical
