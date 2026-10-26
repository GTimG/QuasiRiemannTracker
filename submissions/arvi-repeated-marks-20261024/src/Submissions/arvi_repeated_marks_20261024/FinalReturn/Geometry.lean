/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnConstants
set_option autoImplicit false
namespace QRH.RepeatedMarks.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.RepeatedMarks.Return.theta
  ell := QRH.RepeatedMarks.Return.ell
  x := QRH.RepeatedMarks.Return.x
  y := QRH.RepeatedMarks.Return.y
  ell_pos := by norm_num [QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c]
  sixth_lt_ell := by norm_num [QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c]
  ell_lt_fifth := by norm_num [QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c]
  ell_lt_x := by norm_num [QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c,QRH.RepeatedMarks.Return.h]
  x_lt_y := by norm_num [QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.y,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c,QRH.RepeatedMarks.Return.h]
  y_lt_half := by norm_num [QRH.RepeatedMarks.Return.y,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c,QRH.RepeatedMarks.Return.h]
  x_add_y := by dsimp [QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.y];ring
  dilation_gap := by norm_num [QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.y,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c,QRH.RepeatedMarks.Return.h]
  tuple_margin_neg := by norm_num [QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.y,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.c,QRH.RepeatedMarks.Return.h]
  signal_boundary := QRH.RepeatedMarks.Return.geometry_mellin
end QRH.RepeatedMarks.Return.Geometry
#print axioms QRH.RepeatedMarks.Return.Geometry.finalParameters
