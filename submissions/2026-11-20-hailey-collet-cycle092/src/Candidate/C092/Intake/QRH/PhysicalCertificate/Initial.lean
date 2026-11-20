/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial00
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial01
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial02
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial03
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial04
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial05
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial06
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial07
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial08
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial09
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial10
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial11
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial12
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial13
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial14
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial15
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial16
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial17
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial18
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial19
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial20
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial21
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial22
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial23
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial24
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial25
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial26
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial27
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial28
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial29
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial30
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial31
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial32
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial33
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial34
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial35
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial36
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial37
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial38
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial39
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial40
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial41
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial42
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial43
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial44
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial45
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial46
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial47
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial48
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial49
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial50
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial51
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial52
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial53
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial54
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial55
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial56

/-! Complete original-domain to actual-Q-forest geometric bridge, retaining original-cell ownership. -/

set_option autoImplicit false

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- One complete actual initial partition for each of the 57 source cells. -/
noncomputable def initialTrees : List InitialTree := [initialTree00, initialTree01, initialTree02, initialTree03, initialTree04, initialTree05, initialTree06, initialTree07, initialTree08, initialTree09, initialTree10, initialTree11, initialTree12, initialTree13, initialTree14, initialTree15, initialTree16, initialTree17, initialTree18, initialTree19, initialTree20, initialTree21, initialTree22, initialTree23, initialTree24, initialTree25, initialTree26, initialTree27, initialTree28, initialTree29, initialTree30, initialTree31, initialTree32, initialTree33, initialTree34, initialTree35, initialTree36, initialTree37, initialTree38, initialTree39, initialTree40, initialTree41, initialTree42, initialTree43, initialTree44, initialTree45, initialTree46, initialTree47, initialTree48, initialTree49, initialTree50, initialTree51, initialTree52, initialTree53, initialTree54, initialTree55, initialTree56]

/-- The initial partition table has exactly one entry per original cell. -/
theorem initialTrees_length : initialTrees.length = 57 := by decide

/-- Select an actual source cell with a statically valid finite index. -/
def originalAt (index : Fin 57) : OriginalCell :=
  originalCells.get ⟨index.val, by simpa only [originalCells_length] using index.isLt⟩

/-- Select the owner-preserving partition for the same original cell. -/
noncomputable def initialAt (index : Fin 57) : InitialTree :=
  initialTrees.get ⟨index.val, by simpa only [initialTrees_length] using index.isLt⟩

/-- Every source cell and its corresponding owner-preserving initial partition pass the checker. -/
theorem initialAt_checked (index : Fin 57) :
    (initialAt index).check index.val qForest (originalAt index).box = true := by
  fin_cases index
  · exact initialTree00_checked
  · exact initialTree01_checked
  · exact initialTree02_checked
  · exact initialTree03_checked
  · exact initialTree04_checked
  · exact initialTree05_checked
  · exact initialTree06_checked
  · exact initialTree07_checked
  · exact initialTree08_checked
  · exact initialTree09_checked
  · exact initialTree10_checked
  · exact initialTree11_checked
  · exact initialTree12_checked
  · exact initialTree13_checked
  · exact initialTree14_checked
  · exact initialTree15_checked
  · exact initialTree16_checked
  · exact initialTree17_checked
  · exact initialTree18_checked
  · exact initialTree19_checked
  · exact initialTree20_checked
  · exact initialTree21_checked
  · exact initialTree22_checked
  · exact initialTree23_checked
  · exact initialTree24_checked
  · exact initialTree25_checked
  · exact initialTree26_checked
  · exact initialTree27_checked
  · exact initialTree28_checked
  · exact initialTree29_checked
  · exact initialTree30_checked
  · exact initialTree31_checked
  · exact initialTree32_checked
  · exact initialTree33_checked
  · exact initialTree34_checked
  · exact initialTree35_checked
  · exact initialTree36_checked
  · exact initialTree37_checked
  · exact initialTree38_checked
  · exact initialTree39_checked
  · exact initialTree40_checked
  · exact initialTree41_checked
  · exact initialTree42_checked
  · exact initialTree43_checked
  · exact initialTree44_checked
  · exact initialTree45_checked
  · exact initialTree46_checked
  · exact initialTree47_checked
  · exact initialTree48_checked
  · exact initialTree49_checked
  · exact initialTree50_checked
  · exact initialTree51_checked
  · exact initialTree52_checked
  · exact initialTree53_checked
  · exact initialTree54_checked
  · exact initialTree55_checked
  · exact initialTree56_checked

/-- Every point of each full edge reaches a positive stored direct terminal or an actual Q root with the correct original-cell owner. -/
theorem original_domain_covered (edge : Fin 4) {p : Point} (hp : originalDomain.Contains p) :
    ∃ index : Fin 57, (originalAt index).edge = edge.val ∧
      ((∃ record ∈ (initialAt index).directRecords, record.box.Contains p ∧ 0 < record.margin) ∨
        (∃ root ∈ qForest, root.originalCell = index.val ∧ root.box.Contains p)) := by
  rcases originalCells_cover edge hp with ⟨cell, hc, he, hb⟩
  rcases List.mem_iff_get.mp hc with ⟨index, hi⟩
  let index' : Fin 57 := ⟨index.val, by simpa only [originalCells_length] using index.isLt⟩
  have hcell : originalAt index' = cell := by simpa only [originalAt, index'] using hi
  refine ⟨index', ?_, ?_⟩
  · simpa only [hcell] using he
  · exact (initialAt index').sound index'.val qForest (originalAt index').box
      (initialAt_checked index') (by simpa only [hcell] using hb)

/-- Complete geometric coverage by actual positive stored terminal records, retaining the edge and source-cell provenance. -/
theorem original_domain_covered_by_records (edge : Fin 4) {p : Point} (hp : originalDomain.Contains p) :
    ∃ index : Fin 57, (originalAt index).edge = edge.val ∧
      ((∃ record ∈ (initialAt index).directRecords, record.box.Contains p ∧ 0 < record.margin) ∨
        (∃ root ∈ qForest, root.originalCell = index.val ∧
          ∃ record ∈ root.tree.records, record.box.Contains p ∧ record.accepted = true)) := by
  rcases original_domain_covered edge hp with ⟨index, he, hd | hr⟩
  · exact ⟨index, he, Or.inl hd⟩
  · rcases hr with ⟨root, hm, ho, hb⟩
    have hroot : root.tree.check root.box = true := List.all_eq_true.mp qForest_checked root hm
    exact ⟨index, he, Or.inr ⟨root, hm, ho, root.tree.covers_record root.box hroot hb⟩⟩

/-- A genuine edge-wise physical conclusion follows once the stored direct and refined leaves are given their still-required pointwise price interpretation. -/
theorem original_pointwise_of_route_sound {P : ℕ → Point → Prop}
    (hDirect : ∀ index : Fin 57, ∀ record ∈ (initialAt index).directRecords,
      0 < record.margin → ∀ p, record.box.Contains p → P (originalAt index).edge p)
    (hRefined : ∀ index : Fin 57, ∀ root ∈ qForest, root.originalCell = index.val →
      ∀ record ∈ root.tree.records, record.accepted = true →
        ∀ p, record.box.Contains p → P (originalAt index).edge p)
    (edge : Fin 4) {p : Point} (hp : originalDomain.Contains p) : P edge.val p := by
  rcases original_domain_covered_by_records edge hp with ⟨index, he, hd | hr⟩
  · rcases hd with ⟨record, hm, hb, hv⟩
    simpa only [he] using hDirect index record hm hv p hb
  · rcases hr with ⟨root, hm, ho, record, hrecord, hb, ha⟩
    simpa only [he] using hRefined index root hm ho record hrecord ha p hb

end QRH.PhysicalCertificate
