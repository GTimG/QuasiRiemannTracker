import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Candidate.Local.Qrh.PositiveGap.Return.Constants
set_option autoImplicit false
set_option warn.classDefReducibility false
namespace QRH.PositiveGap.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
variable [TargetC]
noncomputable def finalParameters : Parameters where
  theta := QRH.PositiveGap.Return.theta
  ell := QRH.PositiveGap.Return.ell
  x := QRH.PositiveGap.Return.x
  y := QRH.PositiveGap.Return.y
  ell_pos := by unfold QRH.PositiveGap.Return.ell; linarith [QRH.PositiveGap.Return.c_lo]
  sixth_lt_ell := by unfold QRH.PositiveGap.Return.ell; linarith [QRH.PositiveGap.Return.c_lo]
  ell_lt_fifth := by unfold QRH.PositiveGap.Return.ell; linarith [QRH.PositiveGap.Return.c_hi]
  ell_lt_x := by unfold QRH.PositiveGap.Return.x QRH.PositiveGap.Return.ell QRH.PositiveGap.Return.h; linarith [QRH.PositiveGap.Return.c_hi]
  x_lt_y := by unfold QRH.PositiveGap.Return.x QRH.PositiveGap.Return.y QRH.PositiveGap.Return.ell QRH.PositiveGap.Return.h; linarith [QRH.PositiveGap.Return.c_lo]
  y_lt_half := by unfold QRH.PositiveGap.Return.y QRH.PositiveGap.Return.ell QRH.PositiveGap.Return.h; linarith [QRH.PositiveGap.Return.c_hi]
  x_add_y := by dsimp [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y];ring
  dilation_gap := by unfold QRH.PositiveGap.Return.x QRH.PositiveGap.Return.y QRH.PositiveGap.Return.ell QRH.PositiveGap.Return.h; linarith [QRH.PositiveGap.Return.c_lo, QRH.PositiveGap.Return.c_hi]
  tuple_margin_neg := by unfold QRH.PositiveGap.Return.x QRH.PositiveGap.Return.y QRH.PositiveGap.Return.ell QRH.PositiveGap.Return.h; linarith [QRH.PositiveGap.Return.c_hi]
  signal_boundary := QRH.PositiveGap.Return.geometry_mellin
end QRH.PositiveGap.Return.Geometry
