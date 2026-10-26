/- Repeated marks: fork of Collet's generic return module PhysicalDirect.ChosenMesh (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Arbitrarily fine simultaneous source/count/probe data. Apache-2.0. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open OAI.SevenEighths QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record12518109Count

theorem exists_chosen_data_small_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (extraMesh : ℝ) (hmesh : 0<extraMesh) :
    ∃A : ChosenData,A.sourceMesh≤extraMesh := by
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hgap hκbeta (fun _=>extraMesh) (fun _ _=>hmesh)
  exact ⟨A,hA.le⟩
end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
