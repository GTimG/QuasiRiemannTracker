/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual old-cutoff coefficient-box count and strict boundary bookkeeping. -/
import Candidate.C092.transport.MixedMiddleReturnSmallBoxes
import Candidate.C092.transport.MixedTicketTailsRawPrice
import Candidate.C092.transport.RawTicketMiddleSourceActual
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Cycle25.Numerator Cycle25.Weighted.Numerator
variable [QRH.Record1252270103Return.Geometry.Parameters]
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.MixedTicketTails

/-- The old ticket, never the refined mixed debit, sizes this coefficient bank. -/
def paidBoxLast (r : Row) (xi : ℝ) : ℕ := ⌈originalVcut r/xi⌉₊
def paidBoxUniformLast (xi : ℝ) : ℕ := ⌈RawTicket.vMax/xi⌉₊

theorem original_vcut_uniform {r : Row} (hr : r∈rows) : originalVcut r ≤ RawTicket.vMax := by
  have hb := every_original_band hr (originalSep r)
  have he := row_endpoint_hull hr
  exact (original_thresholds_uniform hb.1 hb.2.1 he.1.1 he.2.1.2 he.2.2.2.2).1

theorem paidBox_cover (r : Row) {xi : ℝ} (hxi : 0<xi) :
    originalVcut r ≤ (paidBoxLast r xi:ℝ)*xi := by
  exact (div_le_iff₀ hxi).mp (Nat.le_ceil _)

theorem paidBox_uniform {r : Row} (hr : r∈rows) {xi : ℝ} (hxi : 0<xi) :
    paidBoxLast r xi+1 ≤ paidBoxUniformLast xi+1 := by
  exact Nat.add_le_add_right (Nat.ceil_mono
    (div_le_div_of_nonneg_right (original_vcut_uniform hr) hxi.le)) 1

/-- No source estimate is needed at or beyond the strict old small edge. -/
theorem small_box_zero_after_cutoff {U xi vcut : ℝ} {n j : ℕ}
    (hU : 1<U) (hxi : 0 ≤ xi) (hcover : vcut ≤ (n:ℝ)*xi)
    (hedge : vcut ≤ (j:ℝ)*xi) {t : ℝ} (ht : 1 ≤ t)
    (hbox : dilationBox U xi n t=j) : ¬t<U^vcut := by
  intro hsmall
  exact not_lt_of_ge hedge (small_true_box_bounds hU hxi hcover ht hsmall hbox).2.2

#print axioms original_vcut_uniform
#print axioms paidBox_cover
#print axioms small_box_zero_after_cutoff
end
end QRH.Cycle092.MixedMiddleReturn
