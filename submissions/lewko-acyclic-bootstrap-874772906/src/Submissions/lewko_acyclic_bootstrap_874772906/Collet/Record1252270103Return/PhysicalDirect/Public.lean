/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.PhysicalDirect.Active
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.PhysicalDirect.ActualBin
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.PhysicalDirect.Selection
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false

open QRH.Record1252270103Return

namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record1252270103Return.GenericArithmetic

/-- The original positive physical slot dictionary is fine enough after every
allowed row-scale rescaling. No total-width or cardinality loss is added. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

end QRH.Record1252270103Return.GenericPhysical.PhysicalDirect

#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.affine_active_box_fourth
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Packet.actual_label_packet_bin_bound
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.scheduled_whole_slots
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.rescaled_slot_mesh
