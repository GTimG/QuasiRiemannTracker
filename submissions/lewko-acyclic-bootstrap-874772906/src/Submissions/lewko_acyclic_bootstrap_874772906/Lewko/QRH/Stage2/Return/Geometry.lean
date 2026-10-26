/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnConstants
set_option autoImplicit false
namespace QRH.LewkoStage2Return.Geometry
class Parameters where
  theta : ℝ
  ell : ℝ
  x : ℝ
  y : ℝ
  ell_pos : 0<ell
  sixth_lt_ell : 1/6<ell
  ell_lt_fifth : ell<1/5
  ell_lt_x : ell<x
  x_lt_y : x<y
  y_lt_half : y<1/2
  x_add_y : x+y=1-ell
  dilation_gap : 0<2*x-y-ell
  tuple_margin_neg : 1+3*ell-2*(x+y)<0
  signal_boundary : theta-(4+y-x)/6=x/2+(y-x)/12
noncomputable section
variable [G : Parameters]
def theta : ℝ := G.theta
def ell : ℝ := G.ell
def x : ℝ := G.x
def y : ℝ := G.y
def signalShift : ℝ := -(4+y-x)/6
def signal (s : ℝ) : ℝ := s+signalShift
theorem ell_pos : 0<ell := G.ell_pos
theorem sixth_lt_ell : 1/6<ell := G.sixth_lt_ell
theorem ell_lt_fifth : ell<1/5 := G.ell_lt_fifth
theorem ell_lt_x : ell<x := G.ell_lt_x
theorem x_lt_y : x<y := G.x_lt_y
theorem y_lt_half : y<1/2 := G.y_lt_half
theorem x_add_y : x+y=1-ell := G.x_add_y
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
  dsimp [signal,signalShift,theta,x,y]
  linarith [G.signal_boundary]
end
noncomputable def finalParameters : Parameters where
  theta := LewkoStage2Finite.theta
  ell := LewkoStage2Finite.ell
  x := LewkoStage2Finite.x
  y := LewkoStage2Finite.y
  ell_pos := by norm_num [LewkoStage2Finite.ell,LewkoStage2Finite.c]
  sixth_lt_ell := by norm_num [LewkoStage2Finite.ell,LewkoStage2Finite.c]
  ell_lt_fifth := by norm_num [LewkoStage2Finite.ell,LewkoStage2Finite.c]
  ell_lt_x := by norm_num [LewkoStage2Finite.x,LewkoStage2Finite.ell,LewkoStage2Finite.c,LewkoStage2Finite.h]
  x_lt_y := by norm_num [LewkoStage2Finite.x,LewkoStage2Finite.y,LewkoStage2Finite.ell,LewkoStage2Finite.c,LewkoStage2Finite.h]
  y_lt_half := by norm_num [LewkoStage2Finite.y,LewkoStage2Finite.ell,LewkoStage2Finite.c,LewkoStage2Finite.h]
  x_add_y := by dsimp [LewkoStage2Finite.x,LewkoStage2Finite.y];ring
  dilation_gap := by norm_num [LewkoStage2Finite.x,LewkoStage2Finite.y,LewkoStage2Finite.ell,LewkoStage2Finite.c,LewkoStage2Finite.h]
  tuple_margin_neg := by norm_num [LewkoStage2Finite.x,LewkoStage2Finite.y,LewkoStage2Finite.ell,LewkoStage2Finite.c,LewkoStage2Finite.h]
  signal_boundary := LewkoStage2Finite.geometry_mellin
end QRH.LewkoStage2Return.Geometry
#print axioms QRH.LewkoStage2Return.Geometry.finalParameters
