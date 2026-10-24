/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Literal initial source moments supply the actual finite numerator and common probe.
Adapted from Gao/Hailey Collet/OpenAI/DaysSky; Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Finite.Bridge
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.JointHeight
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.ChosenMesh
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.FinalCommonProbe
set_option autoImplicit false
open QRH.RH20261023Return

namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open QRH.RH20261023Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.RH20261023Return.GenericCount
open QRH.RH20261023Return.GenericPhysical.FinalAssembly

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
    Cycle25.UniformCommonProbe theta QRH.RH20261023Return.GenericPhysical.Assembly.signalShift :=
  common_probe_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)

theorem beta_le_theta_of_initial_source (hinput : ChosenInitialSourceInput) :
    HeckeZeroSupremum.beta≤theta :=
  beta_le_theta_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)
end
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.common_probe_of_initial_source
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.beta_le_theta_of_initial_source
