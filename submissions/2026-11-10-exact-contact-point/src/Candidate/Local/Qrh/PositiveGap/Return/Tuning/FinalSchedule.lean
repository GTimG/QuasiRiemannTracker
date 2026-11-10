import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.PositiveGap.Return.TransportInstances
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.FinalScheme
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.FinalRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return.Tuning
open QRH.Record1252270103Return
noncomputable section
variable [TargetC]
local instance : QRH.Record1252270103Return.Geometry.Parameters := QRH.PositiveGap.Return.Geometry.finalParameters
local instance : Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN := QRH.PositiveGap.Return.Geometry.finalBounds
local instance : QRH.Record1252270103Return.CountScheme := QRH.PositiveGap.Return.Tuning.finalCountScheme
noncomputable abbrev finalPhysicalSchedule : @Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule QRH.PositiveGap.Return.Geometry.finalParameters QRH.PositiveGap.Return.Tuning.finalCountScheme where
 cap := QRH.PositiveGap.Return.numeratorCap
 cap_nonneg := by norm_num [QRH.PositiveGap.Return.numeratorCap]
 cap_lt_fifth := by norm_num [QRH.PositiveGap.Return.numeratorCap]
 dMinus := QRH.PositiveGap.Return.dm
 physicalB := QRH.PositiveGap.Return.physicalB
 physicalLambda := QRH.PositiveGap.Return.physicalLambda
 dMinus_lower := by norm_num [QRH.PositiveGap.Return.dm]
 dMinus_before_top := by
  change dm ≤ Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h + Qrh.JointDetector.BoundaryPhysical.Return.Geometry.fee
  rw [FinalRows.h_eq, FinalRows.fee_eq]
  unfold dm h
  linarith [c_lo, eps_pos]
 y_before_switch := by
  change y < dm
  unfold dm y h ell
  linarith [c_lo, c_hi]
 switch_before_twoy := by
  change dm < 2 * y
  unfold dm y h ell
  linarith [c_lo, c_hi]
 lambda_bounds := by
  unfold physicalLambda
  constructor <;> linarith [eps_pos, eps_le]
 B_bounds := by
  unfold physicalB
  constructor <;> linarith [eps_pos, eps_le]
 small_plain_global := by
  unfold physicalB physicalLambda numeratorCap
  linarith [eps_pos]
 prime_supply := by
  change (1 / 5 : ℝ) < ell / (Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h + Qrh.JointDetector.BoundaryPhysical.Return.Geometry.fee)
  rw [FinalRows.h_eq, FinalRows.fee_eq]
  rw [lt_div_iff₀ (by unfold h; linarith [c_lo, eps_pos])]
  unfold ell h
  linarith [c_lo, c_hi, eps_pos, eps_le]
 incumbent := by
  change Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.kappa ≤ naturalK / 6
  rw [FinalRows.kappa_eq]
  unfold kappa naturalK
  linarith [c_lo]
 old_rows := by intro d δ p hd hδ hp;exact QRH.PositiveGap.Return.Tuning.final_old_rows hd hδ hp
 new_rows := by intro d δ p hd hδ hp;exact QRH.PositiveGap.Return.Tuning.final_new_rows hd hδ hp
end
end QRH.PositiveGap.Return.Tuning
