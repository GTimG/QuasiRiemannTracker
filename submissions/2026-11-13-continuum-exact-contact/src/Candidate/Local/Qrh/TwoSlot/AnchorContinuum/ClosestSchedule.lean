/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The closest rational candidate instantiates the existing fixed-cost physical
closure. No arbitrary-small-cost analytic passage is required. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ClosestRational
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveGeometry

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.ClosestRational
noncomputable section
open Set Qrh.TwoSlot.AnchorZeroLoss QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Contact (exactLine exactScheme stationaryCutoff)

@[instance_reducible] def parameters : Geometry.Parameters :=
  Contact.ExactReturn.targetGeometry target target_bounds.1.le target_bounds.2
local instance : Geometry.Parameters := parameters
@[instance_reducible] def coarseBounds : BoundsCore :=
  Contact.ExactReturn.targetCoarse target target_bounds.1.le target_bounds.2
local instance : BoundsCore := coarseBounds
local instance : Affine.Return.ImprovedCountScheme exactLine := exactScheme

theorem cost_small : cost ≤ (1/1000000000:ℝ) := by norm_num [cost]
theorem fee_eq : rowFee = cost := by norm_num [rowFee,cost]
theorem h_eq : h = stationaryCutoff :=
  Contact.ExactReturn.target_h target target_bounds.1.le target_bounds.2
theorem dp_eq : dp = stationaryCutoff+cost := by
  change Geometry.h+_ = stationaryCutoff+cost
  have hh : Geometry.h = stationaryCutoff := h_eq
  rw [hh]
  norm_num [cost]

abbrev branches : List Branch := Affine.Return.ImprovedCount.admittedBranches (line := exactLine)
theorem row_eq (D cap d p : ℝ) :
    rowAt branches kappa D cap d p = Contact.ExactReturn.targetRow (2*target-1) target D cap d p :=
  Contact.ExactReturn.generic_row_eq target target_bounds.1.le target_bounds.2 D cap d p
theorem old_capacity_eq (D : ℝ) :
    oldCapacityAt kappa D = Contact.ExactReturn.targetOldCapacity (2*target-1) target D := rfl

/-- Actual physical schedule, with the unchanged strictly positive analytic
fee and extension. The rational target gap pays them with a fixed reserve. -/
@[instance_reducible] def physicalSchedule : PhysicalSchedule (line := exactLine) where
  cap := 3/40
  cap_nonneg := by norm_num
  cap_lt_fifth := by norm_num
  dMinus := 19/25
  physicalB := 1-cost
  physicalLambda := 2+10*cost
  dMinus_lower := by norm_num
  dMinus_before_top := by
    change (19/25:ℝ) ≤ dp
    rw [dp_eq]
    linarith [Contact.stationaryCutoff_bounds.1,cost_pos]
  y_before_switch := by
    change Contact.ExactReturn.targetY target < (19/25:ℝ)
    unfold Contact.ExactReturn.targetY
    linarith [Contact.stationaryCutoff_tight.2,
      (Contact.ExactReturn.target_ell_bounds target_bounds.1.le target_bounds.2).1]
  switch_before_twoy := by
    change (19/25:ℝ) < 2*Contact.ExactReturn.targetY target
    unfold Contact.ExactReturn.targetY
    linarith [Contact.stationaryCutoff_tight.1,
      (Contact.ExactReturn.target_ell_bounds target_bounds.1.le target_bounds.2).2]
  lambda_bounds := by constructor <;> linarith [cost_pos,cost_small]
  B_bounds := by constructor <;> linarith [cost_pos,cost_small]
  small_plain_global := by linarith [cost_pos]
  prime_supply := by
    change (1/5:ℝ) < Contact.ExactReturn.targetEll target/dp
    rw [dp_eq]
    apply (lt_div_iff₀ (by linarith [Contact.stationaryCutoff_pos,cost_pos] :
      0 < stationaryCutoff+cost)).mpr
    linarith [Contact.stationaryCutoff_tight.2,cost_small,
      (Contact.ExactReturn.target_ell_bounds target_bounds.1.le target_bounds.2).1]
  incumbent := by
    change 2*target-1 ≤ QRH.PositiveGap.Return.naturalK/6
    norm_num [target,numerator,denominator,QRH.PositiveGap.Return.naturalK]
  old_rows := by
    intro D d p hD hd hp
    change rowAt branches kappa D (oldCapacityAt kappa D) d p ≤ target-rowFee
    rw [row_eq,old_capacity_eq,fee_eq]
    have hr := Contact.ExactReturn.target_old_rows target_bounds.1.le hD hd hp
    linarith [target_gap,cost_pos]
  new_rows := by
    intro D d p hD hd hp
    change rowAt branches kappa D
      (min ((3/40)*D) ((2*Contact.ExactReturn.targetY target-(2-(1-cost))*D)/(2+10*cost)))
      d p ≤ target-rowFee
    rw [row_eq,fee_eq,show (2:ℝ)-(1-cost) = 1+cost by ring]
    change Contact.ExactReturn.targetRow (2*target-1) target D
      (Contact.ExactReturn.targetCapacity cost target D) d p ≤ target-cost
    have hD' : D ∈ Icc (19/25:ℝ) (stationaryCutoff+cost) := by
      exact ⟨hD.1,hD.2.trans_eq dp_eq⟩
    have hr := Contact.ExactReturn.extended_target_rows cost_pos.le target_bounds.1.le
      cost_pos.le hD' hd hp
    linarith [target_gap,cost_pos]

end
end Qrh.TwoSlot.AnchorContinuum.ClosestRational
#print axioms Qrh.TwoSlot.AnchorContinuum.ClosestRational.physicalSchedule
