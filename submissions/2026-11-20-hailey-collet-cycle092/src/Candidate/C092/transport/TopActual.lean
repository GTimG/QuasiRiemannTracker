/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopChecks00
import Candidate.C092.transport.TopChecks01
import Candidate.C092.transport.TopChecks02
import Candidate.C092.transport.TopChecks03
import Candidate.C092.transport.TopChecks04
import Candidate.C092.transport.TopChecks05
import Candidate.C092.transport.TopChecks06
import Candidate.C092.transport.TopChecks07
import Candidate.C092.transport.TopChecks08
import Candidate.C092.transport.TopChecks09
import Candidate.C092.transport.TopChecks10
import Candidate.C092.transport.TopChecks11
import Candidate.C092.transport.TopChecks12
import Candidate.C092.transport.TopChecks13
import Candidate.C092.transport.TopChecks14
import Candidate.C092.transport.TopChecks15
import Candidate.C092.transport.TopChecks16
import Candidate.C092.transport.TopChecks17
import Candidate.C092.transport.TopChecks18
import Candidate.C092.transport.TopChecks19
import Candidate.C092.transport.TopChecks20
import Candidate.C092.transport.TopChecks21
import Candidate.C092.transport.TopChecks22
import Candidate.C092.transport.TopChecks23
import Candidate.C092.transport.TopChecks24
import Candidate.C092.transport.TopChecks25
import Candidate.C092.transport.TopChecks26
import Candidate.C092.transport.TopChecks27
import Candidate.C092.transport.TopChecks28
import Candidate.C092.transport.TopChecks29
import Candidate.C092.transport.TopChecks30
import Candidate.C092.transport.TopChecks31
import Candidate.C092.transport.TopPhysical
import Candidate.C092.transport.TopBinding

/-! Assembly of all authentic mixed top-price certificates. The exact row-box
binding uses the original full forest, including all closed boundaries. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Top
open QRH.Cycle092.TopData QRH.PhysicalCertificate
noncomputable section

theorem all_rows_checked : rows.all check = true := by
  simp only [rows,List.all_append,group00_checked, group01_checked, group02_checked, group03_checked, group04_checked, group05_checked, group06_checked, group07_checked, group08_checked, group09_checked, group10_checked, group11_checked, group12_checked, group13_checked, group14_checked, group15_checked, group16_checked, group17_checked, group18_checked, group19_checked, group20_checked, group21_checked, group22_checked, group23_checked, group24_checked, group25_checked, group26_checked, group27_checked, group28_checked, group29_checked, group30_checked, group31_checked,Bool.and_true]

/-- Exact binding to every original mixed terminal, in unchanged forest order. -/
theorem mixed_boxes_binding :
    rows.map Row.box = ((forestRecords qForest).filter
      (fun leaf => leaf.route == .mixed)).map StoredLeaf.box := by
  exact Binding.boxes_eq

theorem rows_length : rows.length = 9681 := by decide +kernel

/-- Every actual mixed terminal has a checked row with exactly its own rectangle. -/
theorem actual_mixed_row {leaf : StoredLeaf}
    (hm : leaf∈forestRecords qForest) (hr : leaf.route=.mixed) :
    ∃ r∈rows, r.box=leaf.box ∧ check r=true := by
  have hb : leaf.box∈rows.map Row.box := by
    rw [mixed_boxes_binding]
    exact List.mem_map.mpr ⟨leaf,List.mem_filter.mpr ⟨hm,by simp [hr]⟩,rfl⟩
  rcases List.mem_map.mp hb with ⟨r,hm',heq⟩
  exact ⟨r,hm',heq,List.all_eq_true.mp all_rows_checked r hm'⟩

/-- The original Q1 top excess is bounded by frozen B on every authenticated mixed row. -/
theorem every_row_top_budget {r : Row} (hr : r∈rows)
    {h x : ℝ} {point : QRH.Coverage.Point}
    (hh : QRH.Cycle090.hLower≤h) (hh' : h≤QRH.Cycle090.hUpper)
    (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x) :
    QRH.Cycle092.Physical.price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) h-
        QRH.Cycle090.theta≤(r.B:ℝ) :=
  top_budget (List.all_eq_true.mp all_rows_checked r hr) hh hh' hp (actual_contact hx)

/-- Every original mixed terminal has a genuine original-price bound with its own B. -/
theorem all_mixed_top_budget {leaf : StoredLeaf}
    (hm : leaf∈forestRecords qForest) (hr : leaf.route=.mixed) :
    ∃ r∈rows, r.box=leaf.box ∧ ∀ (h x : ℝ) (point : QRH.Coverage.Point),
      QRH.Cycle090.hLower≤h → h≤QRH.Cycle090.hUpper → leaf.box.Contains point →
      QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x →
      QRH.Cycle092.Physical.price h point.1 point.2
        (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
        (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) h-
          QRH.Cycle090.theta≤(r.B:ℝ) := by
  rcases actual_mixed_row hm hr with ⟨r,hm',heq,hc⟩
  refine ⟨r,hm',heq,?_⟩
  intro h x point hh hh' hp hx
  exact top_budget hc hh hh' (heq.symm ▸ hp) (actual_contact hx)

/-- Q2's actual physical bound holds for all 9,681 rows at the original normalized debit. -/
theorem every_row_normalized_debit {r : Row} (hr : r∈rows)
    {h x D : ℝ} {point : QRH.Coverage.Point}
    (hh : QRH.Cycle090.hLower≤h) (hh' : h≤QRH.Cycle090.hUpper)
    (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x)
    (hD : 0≤D) (hDh : D≤h) :
    QRH.Cycle090.positivePart (QRH.Cycle092.Physical.price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) D-
        QRH.Cycle090.theta+QRH.Cycle090.inwardDebit)≤D*debit r :=
  normalized_physical_debit (List.all_eq_true.mp all_rows_checked r hr)
    hh hh' hp (actual_contact hx) hD hDh

end
end QRH.Cycle092.Top
#print axioms QRH.Cycle092.Top.all_mixed_top_budget
#print axioms QRH.Cycle092.Top.every_row_normalized_debit
#print axioms QRH.Cycle092.Top.mixed_boxes_binding
#print axioms QRH.Cycle092.Top.all_rows_checked
