/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCheck00
import Candidate.C092.transport.MixedTicketTailsRawCheck01
import Candidate.C092.transport.MixedTicketTailsRawCheck02
import Candidate.C092.transport.MixedTicketTailsRawCheck03
import Candidate.C092.transport.MixedTicketTailsRawCheck04
import Candidate.C092.transport.MixedTicketTailsRawCheck05
import Candidate.C092.transport.MixedTicketTailsRawCheck06
import Candidate.C092.transport.MixedTicketTailsRawCheck07
import Candidate.C092.transport.MixedTicketTailsRawCheck08
import Candidate.C092.transport.MixedTicketTailsRawCheck09
import Candidate.C092.transport.MixedTicketTailsRawCheck10
import Candidate.C092.transport.MixedTicketTailsRawCheck11
import Candidate.C092.transport.MixedTicketTailsRawCheck12
import Candidate.C092.transport.MixedTicketTailsRawCheck13
import Candidate.C092.transport.MixedTicketTailsRawCheck14
import Candidate.C092.transport.MixedTicketTailsRawCheck15
import Candidate.C092.transport.MixedTicketTailsRawCheck16
import Candidate.C092.transport.MixedTicketTailsRawCheck17
import Candidate.C092.transport.MixedTicketTailsRawCheck18
import Candidate.C092.transport.MixedTicketTailsRawCheck19
import Candidate.C092.transport.MixedTicketTailsRawCheck20
import Candidate.C092.transport.MixedTicketTailsRawCheck21
import Candidate.C092.transport.MixedTicketTailsRawCheck22
import Candidate.C092.transport.MixedTicketTailsRawCheck23
import Candidate.C092.transport.MixedTicketTailsRawCheck24
import Candidate.C092.transport.MixedTicketTailsRawCheck25
import Candidate.C092.transport.MixedTicketTailsRawCheck26
import Candidate.C092.transport.MixedTicketTailsRawCheck27
import Candidate.C092.transport.MixedTicketTailsRawCheck28
import Candidate.C092.transport.MixedTicketTailsRawCheck29
import Candidate.C092.transport.MixedTicketTailsRawCheck30
import Candidate.C092.transport.MixedTicketTailsRawCheck31
set_option autoImplicit false
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData QRH.Cycle092.RawTicket
noncomputable section

theorem all_rows_raw_bridge : rows.all rawBridgeCheck = true := by
  simp only [rows,List.all_append,group00_raw_checked,group01_raw_checked,group02_raw_checked,group03_raw_checked,group04_raw_checked,group05_raw_checked,group06_raw_checked,group07_raw_checked,group08_raw_checked,group09_raw_checked,group10_raw_checked,group11_raw_checked,group12_raw_checked,group13_raw_checked,group14_raw_checked,group15_raw_checked,group16_raw_checked,group17_raw_checked,group18_raw_checked,group19_raw_checked,group20_raw_checked,group21_raw_checked,group22_raw_checked,group23_raw_checked,group24_raw_checked,group25_raw_checked,group26_raw_checked,group27_raw_checked,group28_raw_checked,group29_raw_checked,group30_raw_checked,group31_raw_checked,Bool.and_true]

/-- Every original terminal's ACTUAL price proxy is below its literal original
coarse debit at the original stationary separation. -/
theorem actual_original_debit_bridge {r : Row} (hr : r∈rows) :
    (r.B:ℝ) ≤ oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi (originalSep r) := by
  have h := List.all_eq_true.mp all_rows_raw_bridge r hr
  have hq : r.B ≤ rawDebitProxyQ r := by simpa only [rawBridgeCheck,decide_eq_true_eq] using h
  exact ((Rat.cast_le (K:=ℝ)).mpr hq).trans (raw_proxy_le_old_debit r)
end
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_original_debit_bridge
