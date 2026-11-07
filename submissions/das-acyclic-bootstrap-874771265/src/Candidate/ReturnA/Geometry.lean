/- Stage geometry for Subhanjan Das, AI-assisted with OpenAI Codex.
Original parameter construction: Hailey Collet/Mark Lewko, Apache-2.0. -/
import Candidate.ReturnA.Finite.ReturnConstants
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportGeometry
set_option autoImplicit false
namespace Das.QRH.ReturnA
open QRH.LewkoStage2Return
noncomputable section
@[instance_reducible] noncomputable def parameters : Geometry.Parameters where
  theta := DasStageAFinite.theta
  ell := DasStageAFinite.ell
  x := DasStageAFinite.x
  y := DasStageAFinite.y
  ell_pos := by norm_num [DasStageAFinite.ell,DasStageAFinite.c]
  sixth_lt_ell := by norm_num [DasStageAFinite.ell,DasStageAFinite.c]
  ell_lt_fifth := by norm_num [DasStageAFinite.ell,DasStageAFinite.c]
  ell_lt_x := by norm_num [DasStageAFinite.x,DasStageAFinite.ell,DasStageAFinite.c,DasStageAFinite.h]
  x_lt_y := by norm_num [DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.ell,DasStageAFinite.c,DasStageAFinite.h]
  y_lt_half := by norm_num [DasStageAFinite.y,DasStageAFinite.ell,DasStageAFinite.c,DasStageAFinite.h]
  x_add_y := by dsimp [DasStageAFinite.x,DasStageAFinite.y];ring
  dilation_gap := by norm_num [DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.ell,DasStageAFinite.c,DasStageAFinite.h]
  tuple_margin_neg := by norm_num [DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.ell,DasStageAFinite.c,DasStageAFinite.h]
  signal_boundary := DasStageAFinite.geometry_mellin
theorem bounds : @Geometry.Bounds parameters := by
  refine @Geometry.Bounds.mk parameters ?_ ?_ ?_ ?_ ?_ ?_
  · change (874/1000:ℝ)<DasStageAFinite.theta ∧ DasStageAFinite.theta<7/8
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
  · change (793/1000:ℝ)<1+DasStageAFinite.ell-DasStageAFinite.x ∧ 1+DasStageAFinite.ell-DasStageAFinite.x<802/1000
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
  · change (458/1000:ℝ)<DasStageAFinite.y ∧ DasStageAFinite.y<466/1000
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
  · change (1672/10000:ℝ)<DasStageAFinite.ell ∧ DasStageAFinite.ell<1677/10000
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
  · change (7/100:ℝ)<DasStageAFinite.y/2-(1+DasStageAFinite.ell-DasStageAFinite.x)*(17/50-1/6)-1/50
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
  · change (4/25:ℝ)*DasStageAFinite.x-3/20-51/100*DasStageAFinite.y+67/100*(1+DasStageAFinite.ell-DasStageAFinite.x+1/10000000000)-3/20*DasStageAFinite.ell ≤ DasStageAFinite.theta+(-(4+DasStageAFinite.y-DasStageAFinite.x)/6)-1/200
    norm_num [DasStageAFinite.theta,DasStageAFinite.ell,DasStageAFinite.x,DasStageAFinite.y,DasStageAFinite.c,DasStageAFinite.h]
end
end Das.QRH.ReturnA
#print axioms Das.QRH.ReturnA.bounds
