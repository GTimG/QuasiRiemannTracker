/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.arvi_selected_leaf.Return.Constants
set_option autoImplicit false
namespace QRH.ArviDensity.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.ArviDensity.Return.theta
  ell := QRH.ArviDensity.Return.ell
  x := QRH.ArviDensity.Return.x
  y := QRH.ArviDensity.Return.y
  ell_pos := by norm_num [QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c]
  sixth_lt_ell := by norm_num [QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c]
  ell_lt_fifth := by norm_num [QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c]
  ell_lt_x := by norm_num [QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c,QRH.ArviDensity.Return.h]
  x_lt_y := by norm_num [QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.y,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c,QRH.ArviDensity.Return.h]
  y_lt_half := by norm_num [QRH.ArviDensity.Return.y,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c,QRH.ArviDensity.Return.h]
  x_add_y := by dsimp [QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.y];ring
  dilation_gap := by norm_num [QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.y,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c,QRH.ArviDensity.Return.h]
  tuple_margin_neg := by norm_num [QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.y,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.c,QRH.ArviDensity.Return.h]
  signal_boundary := QRH.ArviDensity.Return.geometry_mellin
end QRH.ArviDensity.Return.Geometry
