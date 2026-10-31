/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module FinalScheme (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): every window face is restricted from one of the two global faces; the separate physical window face is dropped -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
import Candidate.Local.Qrh.PR98Improvement.Return.Tuning.FinalWindows
import Candidate.Local.Qrh.PR98Improvement.Return.WindowSources
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PR98Improvement.Return.Tuning
open QRH.Record1252270103Return QRH.PR98Improvement.ReturnTuning
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
noncomputable abbrev finalCountScheme : CountScheme where
 naturalκ := naturalK/6
 natural_lo := by norm_num [naturalK]
 natural_hi := by norm_num [naturalK]
 windows := finalAdmittedWindows

theorem ReturnCountWindow.toAdmitted_face (w:ReturnCountWindow) :
 (ReturnCountWindow.toAdmitted w).face=countingSource w.branch := rfl

theorem final_windows_common_mesh
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {ε:ℝ} (hε:0<ε) : ∃mesh:ℝ,0<mesh ∧
 ∀w∈finalCountScheme.windows,UnitFaceSource w.face mesh ε := by
 obtain ⟨mesh,hm,hc,hp⟩ := selected_sources_common_mesh hC hP hε
 refine ⟨mesh,hm,?_⟩
 intro w hw
 obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
 change UnitFaceSource (countingSource v.branch) _ ε
 apply unit_source_restrict (supplier_restricts_counting v.branch v.nonold)
 cases v.branch <;> first | exact (v.nonold rfl).elim | exact hc | exact hp
end
end QRH.PR98Improvement.Return.Tuning
