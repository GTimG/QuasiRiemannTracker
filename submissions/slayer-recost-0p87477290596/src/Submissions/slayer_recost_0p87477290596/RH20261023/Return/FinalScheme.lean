/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.FinalWindows
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.WindowSources
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.CountScheme
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return
noncomputable section
open RH20261023Finite QRH.Record12518109Source QRH.Record12518109Existence
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
end QRH.RH20261023Return
#print axioms QRH.RH20261023Return.final_windows_common_mesh
