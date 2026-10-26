/- Repeated marks: fork of Collet's final-stage module FinalScheme (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.FinalWindows
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.WindowSources
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
noncomputable abbrev finalCountScheme : CountScheme where
 naturalκ := naturalK/6
 natural_lo := by norm_num [naturalK]
 natural_hi := by norm_num [naturalK]
 windows := finalAdmittedWindows

theorem ReturnCountWindow.toAdmitted_face (w:ReturnCountWindow) :
 w.toAdmitted.face=countingSource w.branch := rfl

theorem final_windows_common_mesh
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {ε:ℝ} (hε:0<ε) : ∃mesh:ℝ,0<mesh ∧
 UnitFaceSource physicalWindow mesh ε ∧
 ∀w∈finalCountScheme.windows,UnitFaceSource w.face mesh ε := by
 obtain ⟨mesh,hm,hc,hp,_,hphys⟩ := selected_sources_common_mesh hC hP hε
 refine ⟨mesh,hm,hphys,?_⟩
 intro w hw
 obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
 change UnitFaceSource (countingSource v.branch) _ ε
 apply unit_source_restrict (supplier_restricts_counting v.branch v.nonold)
 cases v.branch <;> first | exact (v.nonold rfl).elim | exact hc | exact hp
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.final_windows_common_mesh
