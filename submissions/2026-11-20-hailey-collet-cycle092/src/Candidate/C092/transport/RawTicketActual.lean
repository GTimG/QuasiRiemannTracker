/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCheck00
import Candidate.C092.transport.RawTicketCheck01
import Candidate.C092.transport.RawTicketCheck02
import Candidate.C092.transport.RawTicketCheck03
import Candidate.C092.transport.RawTicketCheck04
import Candidate.C092.transport.RawTicketCheck05
import Candidate.C092.transport.RawTicketCheck06
import Candidate.C092.transport.RawTicketCheck07
import Candidate.C092.transport.RawTicketCheck08
import Candidate.C092.transport.RawTicketCheck09
import Candidate.C092.transport.RawTicketCheck10
import Candidate.C092.transport.RawTicketCheck11
import Candidate.C092.transport.RawTicketCheck12
import Candidate.C092.transport.RawTicketCheck13
import Candidate.C092.transport.RawTicketCheck14
import Candidate.C092.transport.RawTicketCheck15
import Candidate.C092.transport.RawTicketCheck16
import Candidate.C092.transport.RawTicketCheck17
import Candidate.C092.transport.RawTicketCheck18
import Candidate.C092.transport.RawTicketCheck19
import Candidate.C092.transport.RawTicketCheck20
import Candidate.C092.transport.RawTicketCheck21
import Candidate.C092.transport.RawTicketCheck22
import Candidate.C092.transport.RawTicketCheck23
import Candidate.C092.transport.RawTicketCheck24
import Candidate.C092.transport.RawTicketCheck25
import Candidate.C092.transport.RawTicketCheck26
import Candidate.C092.transport.RawTicketCheck27
import Candidate.C092.transport.RawTicketCheck28
import Candidate.C092.transport.RawTicketCheck29
import Candidate.C092.transport.RawTicketCheck30
import Candidate.C092.transport.RawTicketCheck31
import Candidate.C092.transport.RawTicketBand
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle092.TopData

theorem all_rows_hull : rows.all hullCheck = true := by
  simp only [rows,List.all_append,group00_hull, group01_hull, group02_hull, group03_hull, group04_hull, group05_hull, group06_hull, group07_hull, group08_hull, group09_hull, group10_hull, group11_hull, group12_hull, group13_hull, group14_hull, group15_hull, group16_hull, group17_hull, group18_hull, group19_hull, group20_hull, group21_hull, group22_hull, group23_hull, group24_hull, group25_hull, group26_hull, group27_hull, group28_hull, group29_hull, group30_hull, group31_hull,Bool.and_true]

theorem hull_of_row {r : Row} (hr : r∈rows) : Hull r := by
  have h:=List.all_eq_true.mp all_rows_hull r hr
  simpa only [hullCheck,decide_eq_true_eq] using h

theorem row_endpoint_hull {r : Row} (hr : r∈rows) :
    (dLo≤(r.box.uLo:ℝ) ∧ (r.box.uLo:ℝ)≤dHi) ∧
    (dLo≤(r.box.uHi:ℝ) ∧ (r.box.uHi:ℝ)≤dHi) ∧
    (pLo≤(r.box.vLo:ℝ) ∧ (r.box.vLo:ℝ)≤pHi) ∧
    (pLo≤(r.box.vHi:ℝ) ∧ (r.box.vHi:ℝ)≤pHi) := by
  have h:=hull_of_row hr
  have hs:=Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have ha : dLo≤(r.box.uLo:ℝ) := by
    simpa only [dLo,Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr h.1)
  have hb : (r.box.uHi:ℝ)≤dHi := by
    simpa only [dHi,Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr h.2.1)
  have hf : pLo≤(r.box.vLo:ℝ) := by
    simpa only [pLo,Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr h.2.2.1)
  have he : (r.box.vHi:ℝ)≤pHi := by
    simpa only [pHi,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr h.2.2.2.1)
  have hab : (r.box.uLo:ℝ)≤(r.box.uHi:ℝ) := by exact_mod_cast hs.2.2.1.le
  have hfe : (r.box.vLo:ℝ)≤(r.box.vHi:ℝ) := by exact_mod_cast hs.2.2.2.2.2.1.le
  exact ⟨⟨ha,hab.trans hb⟩,⟨ha.trans hab,hb⟩,⟨hf,hfe.trans he⟩,⟨hf.trans hfe,he⟩⟩

/-- Every actual original mixed leaf has a source-bound row with all original
raw-ticket numerical contracts. This retains the original closed rectangle. -/
theorem actual_mixed_ticket {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf∈QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route=.mixed) :
    ∃ r∈rows, r.box=leaf.box ∧ Hull r := by
  rcases Top.actual_mixed_row hm hr with ⟨r,hm',heq,_⟩
  exact ⟨r,hm',heq,hull_of_row hm'⟩

/-- Literal original coarse-band admission on every one of the 9,681 terminals.
The scalar B used for the central gain never enters this old-debit formula. -/
theorem every_original_band {r : Row} (hr : r∈rows) (sep : ℝ) :
    oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤oldDebitCap ∧
    Dmin≤Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep ∧
    Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤QRH.Cycle090.hLower := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  exact ⟨old_debit_bound ha hb hf he,original_conductor_band ha hb hf he⟩

theorem every_original_discarded_branch {r : Row} (hr : r∈rows) (sep : ℝ) :
    let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    ∀ pair∈originalThresholds debit D r.box.uLo r.box.uHi r.box.vHi,
      8*oldFee<pair.1*pair.2-debit := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  exact original_thresholds_paid (every_original_band hr sep).2.1 ha.1 hb.2 he.2

theorem every_original_continuation {r : Row} (hr : r∈rows) (sep thi : ℝ)
    (ht : 0≤thi ∧ thi≤tHi) :
    let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    ∀ gap∈continuationGaps r.box.vLo r.box.vHi thi,
      8*oldFee<3*D*(r.box.uLo:ℝ)*gap/4-debit := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have hd:=every_original_band hr sep
  exact continuation_fees_uniform hd.1 hd.2.1 ha.1 hf he ht

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.all_rows_hull
#print axioms QRH.Cycle092.RawTicket.every_original_band
#print axioms QRH.Cycle092.RawTicket.every_original_discarded_branch
#print axioms QRH.Cycle092.RawTicket.every_original_continuation
