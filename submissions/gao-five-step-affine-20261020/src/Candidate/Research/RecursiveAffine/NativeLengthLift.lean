/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeCoarseSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle63Moment Cycle63InitialMass

/-- The actual label-side exponent is affine with slope one in the
source volume. This permits an explicit, compensated volume majorant. -/
theorem lowLabelSide_length_add (reflected : Bool) (Z A a : ℝ) (first : FirstSourceLabel) :
    lowLabelSide reflected Z (A+a) first=lowLabelSide reflected Z A first+a := by
  unfold lowLabelSide
  ring

namespace NativePaidPathNode
variable {Z : ℝ} (p : NativePaidPathNode Z)

/-- Use a volume majorant while compensating the identical first-label
side by the same amount. The raw outside coefficient is unchanged.
The signed `massLoss` field now records this explicit compensation;
it is not asserted equal to the unadjusted first-mass dyad exponent. -/
def lengthLift (a : ℝ) : NativePaidPathNode Z :=
  { p with
    length := p.length+a
    massLoss := p.massLoss-a
    side := by
      rw [lowLabelSide_length_add]
      linarith only [p.side] }

theorem lengthLift_volumeLength (a : ℝ) :
    (p.lengthLift a).volumeLength=p.volumeLength+p.unit*a := by
  simp only [volumeLength,lengthLift]
  ring

theorem lengthLift_coordinate_zero (a : ℝ) :
    (p.lengthLift a).coordinate 0=p.coordinate 0+p.unit*a := by
  dsimp only [coordinate,lengthLift,actualHighCoordinates,Matrix.cons_val_zero]
  ring_nf

theorem lengthLift_coordinate_one (a : ℝ) :
    (p.lengthLift a).coordinate 1=p.coordinate 1 := rfl

theorem lengthLift_coordinate_two (a : ℝ) :
    (p.lengthLift a).coordinate 2=p.coordinate 2 := rfl

theorem lengthLift_coordinate_three (a : ℝ) :
    (p.lengthLift a).coordinate 3=p.coordinate 3+p.unit*a := by
  simp only [coordinate_three,lengthLift_volumeLength]
  change p.volumeLength+p.unit*a-p.commonLog=p.volumeLength-p.commonLog+p.unit*a
  ring

/-- The precise raw coefficient entering the returned family survives
the majorant normalization. No power of the volume slack is discarded. -/
theorem lengthLift_shiftedOutside (a : ℝ) :
    (p.lengthLift a).shiftedOutside=p.shiftedOutside := by
  dsimp only [shiftedOutside]
  rw [lengthLift_coordinate_zero]
  dsimp only [lengthLift]
  ring

@[simp] theorem lengthLift_scale (a : ℝ) : (p.lengthLift a).scale=p.scale := rfl
@[simp] theorem lengthLift_amplification (a : ℝ) :
    (p.lengthLift a).amplification=p.amplification := rfl
@[simp] theorem lengthLift_commonLog (a : ℝ) : (p.lengthLift a).commonLog=p.commonLog := rfl
@[simp] theorem lengthLift_small (a delta : ℝ) :
    (p.lengthLift a).small delta=p.small delta := rfl

theorem lengthLift_sourceGates (a : ℝ) (ha : 0≤a)
    (hA : p.length+a≤4) (source : p.SourceGates) : (p.lengthLift a).SourceGates where
  unit_le_one := source.unit_le_one
  row_nonneg := source.row_nonneg
  row_le_one := source.row_le_one
  length_nonneg := add_nonneg source.length_nonneg ha
  length_le_four := hA
  amp_nonneg := source.amp_nonneg
  amp_le_one := source.amp_le_one
  loss_nonneg := source.loss_nonneg
  loss_le_quarter := source.loss_le_quarter
  eps_nonneg := source.eps_nonneg
  eps_le_quarter := source.eps_le_quarter
  side_le_quarter := source.side_le_quarter
  first_cap := source.first_cap
  own_second_cap := source.own_second_cap

theorem lengthLift_fineSourceGates (a : ℝ) (fine : p.FineSourceGates) :
    (p.lengthLift a).FineSourceGates where
  loss_le := fine.loss_le
  eps_le := fine.eps_le
  side_le := fine.side_le

/-- This is the original returned raw edge, including deletion and every
finite fee, with the SAME exponent after the compensated volume lift. -/
theorem lengthLift_raw_edge (a deletion fee : ℝ) :
    Z^((p.lengthLift a).scale+(p.lengthLift a).shiftedOutside+deletion+fee)=
      Z^(p.scale+p.shiftedOutside+deletion+fee) := by
  rw [lengthLift_scale,lengthLift_shiftedOutside]

end NativePaidPathNode
end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.NativePaidPathNode.lengthLift_shiftedOutside
#print axioms OAI.SevenEighths.Cycle153JointCount.NativePaidPathNode.lengthLift_sourceGates
