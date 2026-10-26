/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Arbitrarily fine simultaneous source/count/probe data. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.RH20261023Return

namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open OAI.SevenEighths QRH.RH20261023Return.GenericArithmetic QRH.Record12518109Count

theorem exists_chosen_data_small_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (extraMesh : ℝ) (hmesh : 0<extraMesh) :
    ∃A : ChosenData,A.sourceMesh≤extraMesh := by
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hgap hκbeta (fun _=>extraMesh) (fun _ _=>hmesh)
  exact ⟨A,hA.le⟩
end
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.exists_chosen_data_small_mesh
