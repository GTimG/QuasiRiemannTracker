/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Variable positive physical-return costs. Adapted from PR137's PhysicalSchedule
(Sil and predecessor authors, Apache-2.0), retaining the actual count envelope.
The submitted fixed-cost schedule and its source files are unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFeedback
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveAffineInput
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSelection

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- All numerical costs are selected after the strict target gap. The source
face, conductor extension and physical row fee remain positive. -/
class Schedule where
  cost : ℝ
  extension : ℝ
  fee : ℝ
  cost_pos : 0 < cost
  cost_small : cost ≤ 1/1000000000
  extension_pos : 0 < extension
  extension_small : extension ≤ 1/1000000000
  fee_pos : 0 < fee
  y_before_switch : Geometry.y < 19/25
  switch_before_twoy : (19/25:ℝ) < 2*Geometry.y
  prime_supply : (1/5:ℝ) < Geometry.ell/(Geometry.h+extension)
  incumbent : 2*Geometry.theta-1 ≤ scheme.naturalκ
  old_rows : ∀ {d delta p : ℝ}, d ∈ Set.Icc (1/200:ℝ) (19/25) →
    delta ∈ Set.Icc (0:ℝ) (3/4) → p ∈ Set.Icc (0:ℝ) (1/2) →
    rowAt Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches
      (2*Geometry.theta-1) d (oldCapacityAt (2*Geometry.theta-1) d) delta p ≤ Geometry.theta-fee
  new_rows : ∀ {d delta p : ℝ}, d ∈ Set.Icc (19/25:ℝ) (Geometry.h+extension) →
    delta ∈ Set.Icc (0:ℝ) (3/4) → p ∈ Set.Icc (0:ℝ) (1/2) →
    rowAt Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches
      (2*Geometry.theta-1) d
      (min ((3/40)*d) ((2*Geometry.y-(1+cost)*d)/(2+10*cost))) delta p ≤ Geometry.theta-fee

def dm : ℝ := 19/25

variable [S : Schedule (line := line)]
abbrev sourceCost : ℝ := S.cost
abbrev rowFee : ℝ := S.fee
abbrev sourceReserve : ℝ := S.fee/2
abbrev rowPadding : ℝ := S.extension/2
abbrev dp : ℝ := Geometry.h+S.extension
def newCapacity (d : ℝ) : ℝ :=
  min ((3/40)*d) ((2*Geometry.y-(1+S.cost)*d)/(2+10*S.cost))

theorem dp_lt_one [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds] :
    dp (line := line) < 1 := by
  have hh := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.h_interval.2
  change Geometry.h+S.extension < 1
  linarith [S.extension_small]

theorem scaled_capacity (d : ℝ) (hd : 0 < d) :
    d*Selection.zeroCapacity S.cost d = newCapacity (line := line) d :=
  Selection.scaled_zero_capacity hd

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
