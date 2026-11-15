/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Coarse geometry for the averaged-floor extension. The old pointwise floor
inequality is deliberately absent. This is geometry, not a physical mean bound. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.TransportGeometry

set_option autoImplicit false
noncomputable section

namespace Qrh.TwoSlot.AnchorZeroLoss

open QRH.Record1252270103Return

/-- The five coarse fields used outside the old pointwise floor argument. -/
class BoundsCore [Geometry.Parameters] : Prop where
  theta_bounds : 873 / 1000 < Geometry.theta ∧ Geometry.theta < 7 / 8
  h_interval : 793 / 1000 < Geometry.h ∧ Geometry.h < 816 / 1000
  ly_coarse : 458 / 1000 < Geometry.y ∧ Geometry.y < 473 / 1000
  ell_interval : 1672 / 10000 < Geometry.ell ∧ Geometry.ell < 175 / 1000
  small_saving : 7 / 100 < Geometry.y / 2 - Geometry.h * (17 / 50 - 1 / 6) - 1 / 50

/-- Supply the common physical interfaces without the obsolete floor field. -/
instance physicalCoreBounds [Geometry.Parameters] [BoundsCore] :
    Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds :=
  ⟨BoundsCore.theta_bounds, BoundsCore.h_interval, BoundsCore.ly_coarse,
   BoundsCore.ell_interval, BoundsCore.small_saving⟩

/-- Existing checkpoints provide the coarse fields without changing their
stronger legacy geometry contract. -/
def BoundsCore.of_legacy [Geometry.Parameters]
    [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] : BoundsCore :=
  ⟨Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds,
   Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval,
   Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ly_coarse,
   Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ell_interval,
   Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.small_saving⟩

/-- The endpoint-coordinate price of the averaged floor, before auxiliary losses. -/
def floorPrice [Geometry.Parameters] (d : ℝ) : ℝ :=
  51 / 100 - 49 / 150 * Geometry.h + 51 / 100 * Geometry.ell + 33 / 50 * d

/-- The retained coarse box leaves a fixed reserve for the averaged floor,
including the conservative conductor extension and the full loss allowance. -/
theorem floor_margin_coarse [Geometry.Parameters] [BoundsCore] {d : ℝ}
    (hd : d ≤ Geometry.h + 1 / 10000000000) :
    1 / 1000 < Geometry.theta - floorPrice d - 1 / 100000 - 1 / 1000000000000 := by
  have ht := BoundsCore.theta_bounds.1
  have hh := BoundsCore.h_interval.2
  have he := BoundsCore.ell_interval.2
  unfold floorPrice
  linarith

def targetTheta : ℝ := 87334587 / 100000000
def targetH : ℝ := 8153237 / 10000000
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
      1 / 100000 - 1 / 1000000000000 = 9560634199 / 3000000000000 := by
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

end Qrh.TwoSlot.AnchorZeroLoss

#print axioms Qrh.TwoSlot.AnchorZeroLoss.floor_margin_coarse
#print axioms Qrh.TwoSlot.AnchorZeroLoss.target_not_legacy_bounds
