/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Candidate.Local.Qrh.PR98Improvement.Return.Constants
set_option autoImplicit false
namespace QRH.PR98Improvement.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.PR98Improvement.Return.theta
  ell := QRH.PR98Improvement.Return.ell
  x := QRH.PR98Improvement.Return.x
  y := QRH.PR98Improvement.Return.y
  ell_pos := by norm_num [QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c]
  sixth_lt_ell := by norm_num [QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c]
  ell_lt_fifth := by norm_num [QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c]
  ell_lt_x := by norm_num [QRH.PR98Improvement.Return.x,QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c,QRH.PR98Improvement.Return.h]
  x_lt_y := by norm_num [QRH.PR98Improvement.Return.x,QRH.PR98Improvement.Return.y,QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c,QRH.PR98Improvement.Return.h]
  y_lt_half := by norm_num [QRH.PR98Improvement.Return.y,QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c,QRH.PR98Improvement.Return.h]
  x_add_y := by dsimp [QRH.PR98Improvement.Return.x,QRH.PR98Improvement.Return.y];ring
  dilation_gap := by norm_num [QRH.PR98Improvement.Return.x,QRH.PR98Improvement.Return.y,QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c,QRH.PR98Improvement.Return.h]
  tuple_margin_neg := by norm_num [QRH.PR98Improvement.Return.x,QRH.PR98Improvement.Return.y,QRH.PR98Improvement.Return.ell,QRH.PR98Improvement.Return.c,QRH.PR98Improvement.Return.h]
  signal_boundary := QRH.PR98Improvement.Return.geometry_mellin
end QRH.PR98Improvement.Return.Geometry
