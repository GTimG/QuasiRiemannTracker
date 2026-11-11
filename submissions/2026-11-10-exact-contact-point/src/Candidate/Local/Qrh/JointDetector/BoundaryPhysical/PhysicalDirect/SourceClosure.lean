import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Finite.Bridge
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.JointHeight
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.ChosenMesh
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.FinalCommonProbe
set_option autoImplicit false
open QRH.Record1252270103Return
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
def ChosenInitialSourceInput : Prop :=
  theta<HeckeZeroSupremum.beta → ∃A : ChosenData,
    (∀w∈scheme.windows, LabelInitialMoments A.F w.face A.sourceMesh) ∧
    Source.ActualAffineInput A
theorem chosen_finite_numerator_of_initial_source (hinput : ChosenInitialSourceInput) :
    ChosenFiniteNumeratorInput := by
  intro hgap
  obtain ⟨A,hlabel,hphysical⟩ := hinput hgap
  have hfields : ∀w∈scheme.windows,WeightedAffineFineInput A.F w.face := by
    intro w hw
    exact actual_detector_affine_input_of_initial A.F w.face
      (by change (1/2:ℝ)≤1/2; exact le_rfl) A.sourceMesh A.sourceMesh_pos A.source_fine (hlabel w hw)
  obtain ⟨J,hJ,hfinite⟩ := FiniteNumerator.fixed_numerator_of_affine hgap A hphysical
  refine ⟨A.D,A.F,A.P,J,hJ,?_⟩
  intro η
  obtain ⟨τ,hheight,hcount⟩ := actual_joint_height A hgap hfields J hJ η
  exact ⟨τ,hheight,hfinite τ hheight η hcount⟩
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
