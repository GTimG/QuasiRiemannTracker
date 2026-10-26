/- Literal initial source moments supply the actual finite numerator and common probe.
Adapted from Gao/Hailey Collet/OpenAI/DaysSky; Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Finite.Bridge
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.JointHeight
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.ChosenMesh
import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.FinalCommonProbe
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open QRH.Record1252270103Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open QRH.Record1252270103Return.GenericPhysical.FinalAssembly

/-- Both genuine initial moment inputs are on one source and common mesh.
The fixed data, amplifiers and physical source error precede the character.
Count controls may depend on that character and precede the joint height. -/
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

theorem common_probe_of_initial_source (hinput : ChosenInitialSourceInput) :
    Cycle25.UniformCommonProbe theta QRH.Record1252270103Return.GenericPhysical.Assembly.signalShift :=
  common_probe_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)

theorem beta_le_theta_of_initial_source (hinput : ChosenInitialSourceInput) :
    HeckeZeroSupremum.beta≤theta :=
  beta_le_theta_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)
end
end QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.common_probe_of_initial_source
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.beta_le_theta_of_initial_source
