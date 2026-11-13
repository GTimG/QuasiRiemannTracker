/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Chosen physical data with a proved variable conductor-padding budget.
All inherited source, detector, count and common-height data remain unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSchedule
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.FinalFixedHigh

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI.SevenEighths HeckeFamily
open BoundaryDensitySplitReturn.TransportHighTransport
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [S : Schedule (line := line)]

structure BufferedData extends ChosenData (line := line) where
  padding_budget : rowPadding (line := line)+2*D.t ≤ S.extension
  padding_small : rowPadding (line := line) ≤
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.rowExtension

theorem padded_row_cutoff (A : BufferedData (line := line)) :
    Geometry.h+rowPadding (line := line)+2*A.D.t ≤ dp (line := line) := by
  change Geometry.h+S.extension/2+2*A.D.t ≤ Geometry.h+S.extension
  have hp : S.extension/2+2*A.D.t ≤ S.extension := A.padding_budget
  linarith only [hp]

def FixedFiniteNumeratorInputAt (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀ n : ℕ, 0 < n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _ => F.w) F.W F.W n η

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
