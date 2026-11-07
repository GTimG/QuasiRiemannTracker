/- Stage geometry for Subhanjan Das, AI-assisted with OpenAI Codex.
Original parameter construction: Hailey Collet/Mark Lewko, Apache-2.0. -/
import Candidate.ReturnB.Finite.ReturnConstants
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportGeometry
set_option autoImplicit false
namespace Das.QRH.ReturnB
open QRH.LewkoStage2Return
noncomputable section
@[instance_reducible] noncomputable def parameters : Geometry.Parameters where
  theta := DasStageBFinite.theta
  ell := DasStageBFinite.ell
  x := DasStageBFinite.x
  y := DasStageBFinite.y
  ell_pos := by norm_num [DasStageBFinite.ell,DasStageBFinite.c]
  sixth_lt_ell := by norm_num [DasStageBFinite.ell,DasStageBFinite.c]
  ell_lt_fifth := by norm_num [DasStageBFinite.ell,DasStageBFinite.c]
  ell_lt_x := by norm_num [DasStageBFinite.x,DasStageBFinite.ell,DasStageBFinite.c,DasStageBFinite.h]
  x_lt_y := by norm_num [DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.ell,DasStageBFinite.c,DasStageBFinite.h]
  y_lt_half := by norm_num [DasStageBFinite.y,DasStageBFinite.ell,DasStageBFinite.c,DasStageBFinite.h]
  x_add_y := by dsimp [DasStageBFinite.x,DasStageBFinite.y];ring
  dilation_gap := by norm_num [DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.ell,DasStageBFinite.c,DasStageBFinite.h]
  tuple_margin_neg := by norm_num [DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.ell,DasStageBFinite.c,DasStageBFinite.h]
  signal_boundary := DasStageBFinite.geometry_mellin
theorem bounds : @Geometry.Bounds parameters := by
  refine @Geometry.Bounds.mk parameters ?_ ?_ ?_ ?_ ?_ ?_
  · change (874/1000:ℝ)<DasStageBFinite.theta ∧ DasStageBFinite.theta<7/8
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
  · change (793/1000:ℝ)<1+DasStageBFinite.ell-DasStageBFinite.x ∧ 1+DasStageBFinite.ell-DasStageBFinite.x<802/1000
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
  · change (458/1000:ℝ)<DasStageBFinite.y ∧ DasStageBFinite.y<466/1000
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
  · change (1672/10000:ℝ)<DasStageBFinite.ell ∧ DasStageBFinite.ell<1677/10000
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
  · change (7/100:ℝ)<DasStageBFinite.y/2-(1+DasStageBFinite.ell-DasStageBFinite.x)*(17/50-1/6)-1/50
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
  · change (4/25:ℝ)*DasStageBFinite.x-3/20-51/100*DasStageBFinite.y+67/100*(1+DasStageBFinite.ell-DasStageBFinite.x+1/10000000000)-3/20*DasStageBFinite.ell ≤ DasStageBFinite.theta+(-(4+DasStageBFinite.y-DasStageBFinite.x)/6)-1/200
    norm_num [DasStageBFinite.theta,DasStageBFinite.ell,DasStageBFinite.x,DasStageBFinite.y,DasStageBFinite.c,DasStageBFinite.h]
end
end Das.QRH.ReturnB
#print axioms Das.QRH.ReturnB.bounds
