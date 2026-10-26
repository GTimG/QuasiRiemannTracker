/- Arbitrarily fine simultaneous source/count/probe data. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open OAI.SevenEighths QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count

theorem exists_chosen_data_small_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (extraMesh : ℝ) (hmesh : 0<extraMesh) :
    ∃A : ChosenData,A.sourceMesh≤extraMesh := by
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hgap hκbeta (fun _=>extraMesh) (fun _ _=>hmesh)
  exact ⟨A,hA.le⟩
end
end QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.exists_chosen_data_small_mesh
