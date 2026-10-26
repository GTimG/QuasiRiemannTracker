/- Private Mark Lewko parameter instance, 2026-10-22.
Analytic/source interfaces: Hailey Collet, Apache-2.0; retained notices in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Graph
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.SourceInlet
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Endpoint
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Lewko.QRH.Stage2
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph
open QRH.Record12518109Existence

theorem global_suppliers
 (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hroot : 6*(2*HeckeZeroSupremum.beta-1) ≤ (112431873/25000000:ℝ))
 (hinternal : 6*(2*HeckeZeroSupremum.beta-1) ≤ finalK) :
 UniformUnitFaceSource QRH.LewkoStage2Return.countGlobal ∧
 UniformUnitFaceSource QRH.LewkoStage2Return.physicalGlobal := by
 have hn : P source000 := by
  simpa [P,source000] using natural_global_source (112431873/25000000:ℝ)
   (by norm_num) (by norm_num) hbeta hroot
 have hg : ParentGood source000 := by norm_num [ParentGood,source000]
 have h := selected_sources_from_rules (fun s => ParentGood s ∧ P s) ⟨hg,hn⟩
  (fun n low high hv ha hl hh => ⟨parent_good_of_source_valid hv,
   QRH.Record1252270103Source.Endpoint.nf_step n low high hbeta hinternal hv hl.1
    (Or.inr ha) hl.2 (fun h hh' => (hh h hh').2)⟩)
 have hC := h.1.2
 have hP := h.2.2
 change UniformUnitFaceSource _ at hC hP
 constructor
 · convert hC using 1 <;>
    norm_num [QRH.Record1252270103Source.globalFace,source220,
     QRH.LewkoStage2Return.countGlobal,QRH.LewkoStage2Return.globalFace,
     LewkoStage2Finite.countCB,LewkoStage2Finite.countCL]
 · convert hP using 1 <;>
    norm_num [QRH.Record1252270103Source.globalFace,source221,
     QRH.LewkoStage2Return.physicalGlobal,QRH.LewkoStage2Return.globalFace,
     LewkoStage2Finite.physicalB,LewkoStage2Finite.physicalLambda]
end
end Lewko.QRH.Stage2
#print axioms Lewko.QRH.Stage2.global_suppliers
