import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Active
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.ActualBin
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Selection
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open QRH.Record1252270103Return
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
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
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
