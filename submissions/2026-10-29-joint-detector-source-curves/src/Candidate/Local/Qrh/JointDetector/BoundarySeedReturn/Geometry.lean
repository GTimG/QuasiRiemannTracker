/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Constants

/-!
# Rational geometry for the source-based return

The geometry uses fixed rational parameters.
The endpoint assembly supplies the actual source providers.
-/

namespace Qrh.JointDetector.BoundarySeedReturn

noncomputable section
set_option autoImplicit false

theorem theta_value : theta = (43691785149423/50000000000000 : ℝ) := rfl

theorem endpoint_gain :
    (4369779/5000000 : ℝ) - theta = 6004850577/50000000000000 := by
  norm_num [theta]

/-- The actual generic return geometry, without using the old endpoint instance. -/
@[instance_reducible] def parameters : QRH.Record1252270103Return.Geometry.Parameters where
  theta := theta
  ell := ell
  x := x
  y := y
  ell_pos := by norm_num [ell, theta]
  sixth_lt_ell := by norm_num [ell, theta]
  ell_lt_fifth := by norm_num [ell, theta]
  ell_lt_x := by norm_num [x, ell, theta, h]
  x_lt_y := by norm_num [x, y, ell, theta, h]
  y_lt_half := by norm_num [y, ell, theta, h]
  x_add_y := by dsimp [x, y]; ring
  dilation_gap := by norm_num [x, y, ell, theta, h]
  tuple_margin_neg := by norm_num [x, y, ell, theta, h]
  signal_boundary := by norm_num [x, y, ell, theta, h]

@[simp] theorem parameters_theta :
    @QRH.Record1252270103Return.Geometry.theta parameters = theta := rfl

@[simp] theorem parameters_ell :
    @QRH.Record1252270103Return.Geometry.ell parameters = ell := rfl

@[simp] theorem parameters_x :
    @QRH.Record1252270103Return.Geometry.x parameters = x := rfl

@[simp] theorem parameters_y :
    @QRH.Record1252270103Return.Geometry.y parameters = y := rfl

@[simp] theorem parameters_h :
    @QRH.Record1252270103Return.Geometry.h parameters = h := by
  dsimp [QRH.Record1252270103Return.Geometry.h, parameters, x]
  ring

@[simp] theorem parameters_dPlus :
    @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus parameters = dp := by
  change @QRH.Record1252270103Return.Geometry.h parameters + 1/10000000000000000000000 = dp
  rw [parameters_h]
  rfl

/-- The six generic coarse-box and complementary-term fields at the new geometry. -/
theorem bounds : @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN parameters := by
  refine @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.mk parameters ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,
      QRH.Record1252270103Return.Geometry.h, QRH.Record1252270103Return.Geometry.ell,
      QRH.Record1252270103Return.Geometry.x, QRH.Record1252270103Return.Geometry.y,
      Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus, QRH.Record1252270103Return.Geometry.signal,
      QRH.Record1252270103Return.Geometry.signalShift, parameters,
      theta, ell, x, y, h] <;> norm_num

end

end Qrh.JointDetector.BoundarySeedReturn
