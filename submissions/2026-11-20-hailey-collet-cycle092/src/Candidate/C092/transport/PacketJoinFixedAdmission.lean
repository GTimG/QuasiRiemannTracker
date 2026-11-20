/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Bind counted direct slices to the original actual finite return leaves. -/
import Candidate.C092.transport.PacketJoinFixedFinalFee
import Candidate.C092.transport.PacketJoinE49FinalFee
import Candidate.C092.transport.DirectAll
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Coverage QRH.PhysicalCertificate
namespace QRH.Cycle092.PacketJoin

/-- Every actual E49 leaf supplies its checked public paired box. -/
theorem e49_box_of_actual_leaf {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf∈(initialAt index).directRecords) (hr : leaf.route="E49_top")
    {δ p : ℝ} (hp : leaf.box.Contains (δ,p)) :
    ∃ box : Box,box∈pairedBoxes ∧ box.Contains (δ,p) := by
  obtain ⟨_,box,hbox,hin⟩ := pairedTreeCheck_sound _ _ (actual_initial_paired_check index) hm hr
  exact ⟨box,hbox,Box.contains_of_included hin hp⟩

/-- An actual top-edge fixed leaf supplies both original count certificates;
no scalar price or choice of a favorable single face is assumed. -/
theorem fixed_top_admission_of_actual_leaf {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf∈(initialAt index).directRecords) (hr : leaf.route="fixed_interior_detector")
    (he : (originalAt index).edge=3)
    {δ p : ℝ} (hp : leaf.box.Contains (δ,p)) : fixedTopAdmission δ p := by
  have hc := otherTreeCheck_sound _ _ (actual_initial_other_check index) hm
  have checks : certificateCovers .fixedS (originalAt index).edge leaf.box=true ∧
      certificateCovers .fixedA (originalAt index).edge leaf.box=true := by
    simpa [otherLeafCheck,hr] using hc
  obtain ⟨cS,hmS,hrS,heS,hinS⟩ := certificateCovers_sound _ _ _ checks.1
  obtain ⟨cA,hmA,hrA,heA,hinA⟩ := certificateCovers_sound _ _ _ checks.2
  refine ⟨cS,cA,hmS,hrS,?_,Box.contains_of_included hinS hp,hmA,hrA,?_,Box.contains_of_included hinA hp⟩
  · exact Fin.ext (heS.trans he)
  · exact Fin.ext (heA.trans he)
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.e49_box_of_actual_leaf
#print axioms QRH.Cycle092.PacketJoin.fixed_top_admission_of_actual_leaf
