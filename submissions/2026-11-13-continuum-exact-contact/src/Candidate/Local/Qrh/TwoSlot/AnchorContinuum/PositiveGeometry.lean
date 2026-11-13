/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual return geometry for targets approaching the exact algebraic endpoint.
The obsolete pointwise floor field is not used. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveLowerReturn
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.BoundsCore
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Schedule

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss
local instance : Affine.Return.ImprovedCountScheme exactLine := exactScheme

def targetX (t : ℝ) : ℝ := 1+targetEll t-stationaryCutoff

theorem target_ell_bounds {t : ℝ} (ht : theta ≤ t) (htop : t ≤ (87334587/100000000:ℝ)) :
    (17328/100000:ℝ) < targetEll t ∧ targetEll t < 17329/100000 := by
  have hi := theta_isolated.1
  norm_num [lower] at hi
  unfold targetEll
  constructor <;> linarith

/-- All literal geometric obligations for every target in the final corridor. -/
@[instance_reducible] def targetGeometry (t : ℝ) (ht : theta ≤ t)
    (htop : t ≤ (87334587/100000000:ℝ)) : QRH.Record1252270103Return.Geometry.Parameters where
  theta := t
  ell := targetEll t
  x := targetX t
  y := targetY t
  ell_pos := by linarith [(target_ell_bounds ht htop).1]
  sixth_lt_ell := by linarith [(target_ell_bounds ht htop).1]
  ell_lt_fifth := by linarith [(target_ell_bounds ht htop).2]
  ell_lt_x := by
    dsimp [targetX]
    linarith [stationaryCutoff_tight.2]
  x_lt_y := by
    dsimp [targetX,targetY]
    linarith [stationaryCutoff_tight.1,(target_ell_bounds ht htop).2]
  y_lt_half := by
    dsimp [targetY]
    linarith [stationaryCutoff_tight.2,(target_ell_bounds ht htop).1]
  x_add_y := by dsimp [targetX,targetY]; ring
  dilation_gap := by
    dsimp [targetX,targetY]
    linarith [stationaryCutoff_tight.2,(target_ell_bounds ht htop).1]
  tuple_margin_neg := by
    dsimp [targetX,targetY]
    linarith [(target_ell_bounds ht htop).2]
  signal_boundary := by dsimp [targetX,targetY,targetEll]; ring

theorem target_h (t : ℝ) (ht : theta ≤ t) (htop : t ≤ (87334587/100000000:ℝ)) :
    @QRH.Record1252270103Return.Geometry.h (targetGeometry t ht htop) = stationaryCutoff := by
  change 1+targetEll t-targetX t = stationaryCutoff
  unfold targetX
  ring

/-- The genuine coarse geometry contract, including the averaged floor's
geometric inputs, holds uniformly throughout the corridor. -/
@[instance_reducible] def targetCoarse (t : ℝ) (ht : theta ≤ t)
    (htop : t ≤ (87334587/100000000:ℝ)) :
    @Qrh.TwoSlot.AnchorZeroLoss.BoundsCore (targetGeometry t ht htop) := by
  refine @Qrh.TwoSlot.AnchorZeroLoss.BoundsCore.mk (targetGeometry t ht htop) ?_ ?_ ?_ ?_ ?_
  · change (873/1000:ℝ) < t ∧ t < 7/8
    have hi := theta_isolated.1
    norm_num [lower] at hi
    constructor <;> linarith
  · rw [target_h]
    exact ⟨by linarith [stationaryCutoff_tight.1],by linarith [stationaryCutoff_tight.2]⟩
  · change (458/1000:ℝ) < targetY t ∧ targetY t < 473/1000
    dsimp [targetY]
    have he := target_ell_bounds ht htop
    constructor <;> linarith [stationaryCutoff_tight.1,stationaryCutoff_tight.2,he.1,he.2]
  · change (1672/10000:ℝ) < targetEll t ∧ targetEll t < 175/1000
    have he := target_ell_bounds ht htop
    constructor <;> linarith [he.1,he.2]
  · rw [target_h]
    change (7/100:ℝ) < targetY t/2-stationaryCutoff*(17/50-1/6)-1/50
    dsimp [targetY]
    linarith [stationaryCutoff_tight.1,(target_ell_bounds ht htop).2]

/-- The transported row is exactly the generic physical schedule expression,
with the actual admitted branch list. -/
theorem generic_row_eq (t : ℝ) (ht : theta ≤ t)
    (htop : t ≤ (87334587/100000000:ℝ)) (D cap d p : ℝ) :
    @Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowAt
      (targetGeometry t ht htop)
      (Affine.Return.ImprovedCount.admittedBranches (line := exactLine))
      (2*t-1) D cap d p = targetRow (2*t-1) t D cap d p := by
  change (1/2+13*(1+targetEll t-targetX t)/75-targetY t/2-targetEll t/2-
    9*D/100+d/2+d*p*(targetEll t-cap/2)+3*D*envelopeAt (2*t-1) d p/4) = _
  have hh : 1+targetEll t-targetX t = stationaryCutoff := by unfold targetX; ring
  rw [hh]
  unfold targetRow targetRowWithFixedCount
  ring

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.targetGeometry
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.targetCoarse
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.generic_row_eq
