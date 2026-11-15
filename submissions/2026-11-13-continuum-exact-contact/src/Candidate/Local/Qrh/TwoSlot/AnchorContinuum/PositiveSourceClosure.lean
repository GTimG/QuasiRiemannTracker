/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Complete physical return closure with the averaged floor. The paired initial
moment suppliers remain the explicit analytic inputs to this theorem. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSourceHigh
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFiniteBridge
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveJointHeight
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.ChosenSource
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter Asymptotics
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
open Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count QRH.Record1252270103Return.GenericCount
variable [Geometry.Parameters] [BoundsCore]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [S : Schedule (line := line)]

/-- Genuine paired initial moments at the common early mesh imply the complete
common probe, using the new floor and the honest finite numerator theorem. -/
theorem common_probe_of_initial_source
    (hinput : theta<HeckeZeroSupremum.beta → ∃A : BufferedData (line := line),
      (∀w∈scheme.windows,LabelInitialMoments A.F w.face A.sourceMesh) ∧
      Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedFineInput line A.F ∧ actualInputAtFace (PositiveSource.physicalFace S.cost) A.toChosenData) :
    Cycle25.UniformCommonProbe theta Assembly.signalShift := by
  intro hgap
  obtain ⟨A,hlabel,himp,hphysical⟩ := hinput hgap
  have hfields : ∀w∈scheme.windows,WeightedAffineFineInput A.F w.face := by
    intro w hw
    exact actual_detector_affine_input_of_initial A.F w.face
      (by change (1/2:ℝ)≤1/2; exact le_rfl) A.sourceMesh A.sourceMesh_pos A.source_fine (hlabel w hw)
  obtain ⟨Jf,hJf,hfinite⟩ := FiniteNumerator.fixed_numerator_of_affine hgap A hphysical
  obtain ⟨Jh,hJh,hhigh⟩ := actual_sourceProbe_high_of_finite hgap A
  let loss := (HeckeZeroSupremum.beta-theta)/2
  have hloss : 0<loss := by dsimp [loss]; linarith
  have hsmall : loss<HeckeZeroSupremum.beta-theta := by dsimp [loss]; linarith
  refine ⟨loss,A.P.sigma,hloss,hsmall,A.P.sigma_pos,?_⟩
  apply fixed_source_contract A.D A.F loss A.P.sigma hloss
  intro η
  obtain ⟨tau,hh,hcount⟩ := actual_joint_height A hgap hfields himp (Jf+Jh) (by positivity) η
  have hhf : HeightAdmissible A.D A.P Jf tau := height_admissible_mono hh (by linarith)
  have hhh : HeightAdmissible A.D A.P Jh tau := height_admissible_mono hh (by linarith)
  exact hhigh tau hhh η (hfinite tau hhf η hcount)

/-- Complete return consumer; this has no legacy floor geometry premise.
This theorem is conditional on the displayed genuine initial moment suppliers. -/
theorem beta_le_theta_of_initial_source
    (hinput : theta<HeckeZeroSupremum.beta → ∃A : BufferedData (line := line),
      (∀w∈scheme.windows,LabelInitialMoments A.F w.face A.sourceMesh) ∧
      Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedFineInput line A.F ∧ actualInputAtFace (PositiveSource.physicalFace S.cost) A.toChosenData) :
    HeckeZeroSupremum.beta≤theta := by
  exact Cycle25.beta_le_of_common_probe
    (show (1/2:ℝ)≤theta by linarith [BoundsCore.theta_bounds.1])
    BoundsCore.theta_bounds.2.le (common_probe_of_initial_source hinput)

end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.common_probe_of_initial_source
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.beta_le_theta_of_initial_source
