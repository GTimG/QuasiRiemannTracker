/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourceClosure (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Literal initial source moments supply the actual finite numerator and common probe.
Adapted from Gao/Hailey Collet/OpenAI/DaysSky; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.Finite.Bridge
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.JointHeight
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.ChosenMesh
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Transport.FinalCommonProbe
set_option autoImplicit false
open QRH.Record1252270103Return

namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.FinalAssembly

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
    Cycle25.UniformCommonProbe theta Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.Assembly.signalShift :=
  common_probe_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)

theorem beta_le_theta_of_initial_source (hinput : ChosenInitialSourceInput) :
    HeckeZeroSupremum.beta≤theta :=
  beta_le_theta_of_finite_numerator (chosen_finite_numerator_of_initial_source hinput)
end
end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
