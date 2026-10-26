/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Geometry
namespace QRH.LewkoStage1Return.Geometry
@[instance_reducible] noncomputable def intermediateParameters : Parameters where
 theta := 8747759/10000000
 ell := 1256723/7500000
 x := 5517391/15000000
 y := 6969163/15000000
 ell_pos := by norm_num
 sixth_lt_ell := by norm_num
 ell_lt_fifth := by norm_num
 ell_lt_x := by norm_num
 x_lt_y := by norm_num
 y_lt_half := by norm_num
 x_add_y := by norm_num
 dilation_gap := by norm_num
 tuple_margin_neg := by norm_num
 signal_boundary := by norm_num
end QRH.LewkoStage1Return.Geometry
#print axioms QRH.LewkoStage1Return.Geometry.intermediateParameters
