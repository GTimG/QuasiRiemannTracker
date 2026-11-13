/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Coarse geometry at the rational continuum target. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.BoundsCore
set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.RationalReturn
open Qrh.TwoSlot.AnchorZeroLoss QRH.Record1252270103Return
def targetTheta : ℝ := 4366729281 / 5000000000
def targetH : ℝ := 1630649 / 2000000
def targetEll : ℝ := 11 / 3 - 4 * targetTheta
def targetX : ℝ := 1 + targetEll - targetH
def targetY : ℝ := targetH - 2 * targetEll

/-- The complete geometric parameters at the new target. No old floor field
is included in this structure. -/
@[instance_reducible] def targetParameters : Geometry.Parameters where
  theta := targetTheta
  ell := targetEll
  x := targetX
  y := targetY
  ell_pos := by norm_num [targetEll, targetTheta]
  sixth_lt_ell := by norm_num [targetEll, targetTheta]
  ell_lt_fifth := by norm_num [targetEll, targetTheta]
  ell_lt_x := by norm_num [targetX, targetEll, targetH, targetTheta]
  x_lt_y := by norm_num [targetX, targetY, targetEll, targetH, targetTheta]
  y_lt_half := by norm_num [targetY, targetEll, targetH, targetTheta]
  x_add_y := by unfold targetX targetY; ring
  dilation_gap := by norm_num [targetX, targetY, targetEll, targetH, targetTheta]
  tuple_margin_neg := by norm_num [targetX, targetY, targetEll, targetH, targetTheta]
  signal_boundary := by norm_num [targetX, targetY, targetEll, targetH, targetTheta]

/-- The new geometry has all five retained coarse properties. -/
@[instance_reducible] def targetBoundsCore : @BoundsCore targetParameters := by
  refine @BoundsCore.mk targetParameters ?_ ?_ ?_ ?_ ?_
  · change 873 / 1000 < targetTheta ∧ targetTheta < 7 / 8
    norm_num [targetTheta]
  · change 793 / 1000 < 1 + targetEll - targetX ∧ 1 + targetEll - targetX < 816 / 1000
    norm_num [targetTheta, targetH, targetX, targetEll]
  · change 458 / 1000 < targetY ∧ targetY < 473 / 1000
    norm_num [targetY, targetTheta, targetH, targetEll]
  · change 1672 / 10000 < targetEll ∧ targetEll < 175 / 1000
    norm_num [targetTheta, targetEll]
  · change 7 / 100 < targetY / 2 - (1 + targetEll - targetX) * (17 / 50 - 1 / 6) - 1 / 50
    norm_num [targetY, targetTheta, targetH, targetX, targetEll]

/-- The conservative exact margin from the written floor argument. This
identity checks the geometric price and does not stand in for the packet proof. -/
theorem target_floor_margin_exact :
    @Geometry.theta targetParameters -
      @floorPrice targetParameters (targetH + 1 / 10000000000) -
      1 / 100000 - 1 / 1000000000000 = 9559708343 / 3000000000000 := by
  change targetTheta - (51 / 100 - 49 / 150 * (1 + targetEll - targetX) +
    51 / 100 * targetEll + 33 / 50 * (targetH + 1 / 10000000000)) -
    1 / 100000 - 1 / 1000000000000 = _
  norm_num [targetTheta, targetH, targetX, targetEll]

/-- The old pointwise floor class is false at this geometry. New consumers
must use the averaged-floor supplier instead of obtaining this instance. -/
theorem target_not_legacy_bounds :
    ¬ @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN targetParameters := by
  intro h
  have hf := @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.floor_margin
    targetParameters h
  have ht : @Geometry.theta targetParameters = targetTheta := rfl
  have hx : @Geometry.x targetParameters = targetX := rfl
  have hy : @Geometry.y targetParameters = targetY := rfl
  have he : @Geometry.ell targetParameters = targetEll := rfl
  have hh : @Geometry.h targetParameters = targetH := by
    change 1 + targetEll - targetX = targetH
    unfold targetX; ring
  unfold Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus
    Geometry.signal Geometry.signalShift at hf
  rw [ht, hx, hy, he, hh] at hf
  norm_num [targetTheta, targetH, targetX, targetY, targetEll] at hf

end Qrh.TwoSlot.AnchorContinuum.RationalReturn
