import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Candidate.Local.Qrh.PositiveGap.Return.Geometry
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Geometry
noncomputable section
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
variable [TargetC]
local instance : Parameters := finalParameters
lemma fee_eq_eps : Qrh.JointDetector.BoundaryPhysical.Return.Geometry.fee = QRH.PositiveGap.Return.eps := by
  change (1081 - (852 * (1 - QRH.PositiveGap.Return.theta) - 75) ^ 2) / 10000000000 = QRH.PositiveGap.Return.eps
  unfold QRH.PositiveGap.Return.theta QRH.PositiveGap.Return.eps QRH.PositiveGap.Return.gap
  ring
lemma h_eq : QRH.Record1252270103Return.Geometry.h = QRH.PositiveGap.Return.h := by
  change 1 + QRH.PositiveGap.Return.ell - QRH.PositiveGap.Return.x = QRH.PositiveGap.Return.h
  unfold QRH.PositiveGap.Return.x
  ring
theorem finalBounds : Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN where
  fee_pos := by rw [fee_eq_eps]; exact QRH.PositiveGap.Return.eps_pos
  fee_le := by rw [fee_eq_eps]; exact QRH.PositiveGap.Return.eps_le
  theta_bounds := by
    change 873 / 1000 < QRH.PositiveGap.Return.theta ∧ QRH.PositiveGap.Return.theta < 7 / 8
    unfold QRH.PositiveGap.Return.theta
    exact ⟨by linarith [QRH.PositiveGap.Return.c_hi], by linarith [QRH.PositiveGap.Return.c_lo]⟩
  h_interval := by
    rw [h_eq]
    unfold QRH.PositiveGap.Return.h
    exact ⟨by linarith [QRH.PositiveGap.Return.c_lo], by linarith [QRH.PositiveGap.Return.c_hi]⟩
  ly_coarse := by
    change 458 / 1000 < QRH.PositiveGap.Return.y ∧ QRH.PositiveGap.Return.y < 473 / 1000
    unfold QRH.PositiveGap.Return.y QRH.PositiveGap.Return.h QRH.PositiveGap.Return.ell
    exact ⟨by linarith [QRH.PositiveGap.Return.c_lo, QRH.PositiveGap.Return.c_hi],
      by linarith [QRH.PositiveGap.Return.c_lo, QRH.PositiveGap.Return.c_hi]⟩
  ell_interval := by
    change 1672 / 10000 < QRH.PositiveGap.Return.ell ∧ QRH.PositiveGap.Return.ell < 175 / 1000
    unfold QRH.PositiveGap.Return.ell
    exact ⟨by linarith [QRH.PositiveGap.Return.c_lo], by linarith [QRH.PositiveGap.Return.c_hi]⟩
  small_saving := by
    rw [h_eq]
    change 7 / 100 < QRH.PositiveGap.Return.y / 2 - QRH.PositiveGap.Return.h * (17 / 50 - 1 / 6) - 1 / 50
    unfold QRH.PositiveGap.Return.y QRH.PositiveGap.Return.h QRH.PositiveGap.Return.ell
    linarith [QRH.PositiveGap.Return.c_lo, QRH.PositiveGap.Return.c_hi]
  floor_margin := by
    unfold Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus
    rw [h_eq, fee_eq_eps]
    change 4 / 25 * QRH.PositiveGap.Return.x - 3 / 20 - 51 / 100 * QRH.PositiveGap.Return.y +
        67 / 100 * (QRH.PositiveGap.Return.h + QRH.PositiveGap.Return.eps) -
        3 / 20 * QRH.PositiveGap.Return.ell ≤
      (QRH.PositiveGap.Return.theta + -(4 + QRH.PositiveGap.Return.y - QRH.PositiveGap.Return.x) / 6) - 1 / 10000
    unfold QRH.PositiveGap.Return.theta QRH.PositiveGap.Return.x QRH.PositiveGap.Return.y
      QRH.PositiveGap.Return.h QRH.PositiveGap.Return.ell
    linarith [QRH.PositiveGap.Return.c_lo, QRH.PositiveGap.Return.c_hi, QRH.PositiveGap.Return.eps_le]
end
end QRH.PositiveGap.Return.Geometry
