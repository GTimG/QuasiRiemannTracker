/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnConstants
set_option autoImplicit false
namespace QRH.Record1252270103Return.Geometry
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
  theta := Record1252270103Finite.theta
  ell := Record1252270103Finite.ell
  x := Record1252270103Finite.x
  y := Record1252270103Finite.y
  ell_pos := by norm_num [Record1252270103Finite.ell,Record1252270103Finite.c]
  sixth_lt_ell := by norm_num [Record1252270103Finite.ell,Record1252270103Finite.c]
  ell_lt_fifth := by norm_num [Record1252270103Finite.ell,Record1252270103Finite.c]
  ell_lt_x := by norm_num [Record1252270103Finite.x,Record1252270103Finite.ell,Record1252270103Finite.c,Record1252270103Finite.h]
  x_lt_y := by norm_num [Record1252270103Finite.x,Record1252270103Finite.y,Record1252270103Finite.ell,Record1252270103Finite.c,Record1252270103Finite.h]
  y_lt_half := by norm_num [Record1252270103Finite.y,Record1252270103Finite.ell,Record1252270103Finite.c,Record1252270103Finite.h]
  x_add_y := by dsimp [Record1252270103Finite.x,Record1252270103Finite.y];ring
  dilation_gap := by norm_num [Record1252270103Finite.x,Record1252270103Finite.y,Record1252270103Finite.ell,Record1252270103Finite.c,Record1252270103Finite.h]
  tuple_margin_neg := by norm_num [Record1252270103Finite.x,Record1252270103Finite.y,Record1252270103Finite.ell,Record1252270103Finite.c,Record1252270103Finite.h]
  signal_boundary := Record1252270103Finite.geometry_mellin
end QRH.Record1252270103Return.Geometry
#print axioms QRH.Record1252270103Return.Geometry.finalParameters
