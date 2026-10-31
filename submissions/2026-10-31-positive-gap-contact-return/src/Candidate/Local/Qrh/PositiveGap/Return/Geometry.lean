/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Candidate.Local.Qrh.PositiveGap.Return.Constants
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.PositiveGap.Return.theta
  ell := QRH.PositiveGap.Return.ell
  x := QRH.PositiveGap.Return.x
  y := QRH.PositiveGap.Return.y
  ell_pos := by norm_num [QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c]
  sixth_lt_ell := by norm_num [QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c]
  ell_lt_fifth := by norm_num [QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c]
  ell_lt_x := by norm_num [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c,QRH.PositiveGap.Return.h]
  x_lt_y := by norm_num [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c,QRH.PositiveGap.Return.h]
  y_lt_half := by norm_num [QRH.PositiveGap.Return.y,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c,QRH.PositiveGap.Return.h]
  x_add_y := by dsimp [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y];ring
  dilation_gap := by norm_num [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c,QRH.PositiveGap.Return.h]
  tuple_margin_neg := by norm_num [QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.c,QRH.PositiveGap.Return.h]
  signal_boundary := QRH.PositiveGap.Return.geometry_mellin
end QRH.PositiveGap.Return.Geometry
