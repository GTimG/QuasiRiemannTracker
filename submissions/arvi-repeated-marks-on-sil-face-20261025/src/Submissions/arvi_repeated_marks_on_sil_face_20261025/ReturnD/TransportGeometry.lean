/- Repeated marks: fork of Collet's generic return module TransportGeometry (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.IntermediateGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.TransportGeometry
namespace QRH.Record1252270103Return.Geometry
noncomputable section
variable [Parameters]
/-- Collet's coarse parameter bounds (`Bounds`, Record1252270103Return/TransportGeometry.lean),
relaxed at the upper ends of `h`, `y` and `ell`. -/
class BoundsR : Prop where
 theta_bounds : 874/1000<theta ∧ theta<7/8
 h_interval : 793/1000<h ∧ h<803/1000
 ly_coarse : 458/1000<y ∧ y<467/1000
 ell_interval : 1672/10000<ell ∧ ell<1690/10000
 small_saving : 7/100<y/2-h*(17/50-1/6)-1/50
 floor_margin : 4/25*x-3/20-51/100*y+67/100*dPlus-3/20*ell ≤ signal theta-1/200
end
end QRH.Record1252270103Return.Geometry

namespace RepeatedMarksReturn.Transport.Arithmetic
noncomputable section
open QRH.Record1252270103Return
variable [Geometry.Parameters] [Geometry.BoundsR]
abbrev theta : ℝ := Geometry.theta
abbrev ell : ℝ := Geometry.ell
abbrev x : ℝ := Geometry.x
abbrev y : ℝ := Geometry.y
abbrev h : ℝ := Geometry.h
abbrev dPlus : ℝ := Geometry.dPlus
theorem ell_eq : ell=11/3-4*theta := by
 have hs := Geometry.signal_at_boundary
 dsimp [Geometry.signal,Geometry.signalShift] at hs
 linarith [Geometry.x_add_y]
theorem x_eq : x=1+ell-h := by dsimp [h,Geometry.h];ring
theorem y_eq : y=h-2*ell := by dsimp [h,Geometry.h];linarith [Geometry.x_add_y]
theorem dPlus_eq : dPlus=h+1/10000000000 := rfl
theorem ell_pos : 0<ell := Geometry.ell_pos
theorem ell_lt_x : ell<x := Geometry.ell_lt_x
theorem x_lt_y : x<y := Geometry.x_lt_y
theorem y_lt_two_x : y<2*x := by
 have hg : 0<2*x-y-ell := Geometry.Parameters.dilation_gap
 have he : 0<ell := Geometry.ell_pos
 linarith
theorem y_lt_half : y<1/2 := Geometry.y_lt_half
theorem half_lt_h : 1/2<h := by linarith [Geometry.BoundsR.h_interval]
theorem h_lt_two_y : h<2*y := by linarith [Geometry.BoundsR.h_interval,Geometry.BoundsR.ly_coarse]
theorem sixth_lt_ell : 1/6<ell := Geometry.sixth_lt_ell
theorem ell_lt_fifth : ell<1/5 := Geometry.ell_lt_fifth
theorem four_ell_lt_h : 4*ell<h := by
 have hh : 793/1000<h := Geometry.BoundsR.h_interval.1
 have he : ell<1690/10000 := Geometry.BoundsR.ell_interval.2
 linarith
theorem x_add_y : x+y=1-ell := Geometry.x_add_y
theorem h_lt_dPlus : h<dPlus := by dsimp [dPlus,Geometry.dPlus];linarith
theorem dPlus_lt_one : dPlus<1 := by dsimp [dPlus,Geometry.dPlus];linarith [Geometry.BoundsR.h_interval]
end
end RepeatedMarksReturn.Transport.Arithmetic
namespace RepeatedMarksReturn.Transport.Assembly
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
open RepeatedMarksReturn.Transport.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
 unfold signalShift
 linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
 unfold signal signalShift
 linarith [ell_eq,x_add_y]
theorem theta_lt_seven_eighths : theta<7/8 := QRH.Record1252270103Return.Geometry.BoundsR.theta_bounds.2
theorem theta_gt_half : 1/2<theta := by linarith [QRH.Record1252270103Return.Geometry.BoundsR.theta_bounds.1]
theorem row_endpoint : h=1-x+ell := by linarith [x_eq]
end
end RepeatedMarksReturn.Transport.Assembly
namespace RepeatedMarksReturn.Transport.Transport
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000
theorem ell_interval : 1672/10000<ell ∧ ell<1690/10000 := QRH.Record1252270103Return.Geometry.BoundsR.ell_interval
theorem h_pos : 0<h := by linarith [QRH.Record1252270103Return.Geometry.BoundsR.h_interval.1]
theorem extended_h_lt_one : h+rowExtension<1 := by dsimp [rowExtension];linarith [QRH.Record1252270103Return.Geometry.BoundsR.h_interval.2]
theorem theta_lower : 874/1000<theta := QRH.Record1252270103Return.Geometry.BoundsR.theta_bounds.1
theorem theta_bounds : 874/1000<theta ∧ theta<7/8 := QRH.Record1252270103Return.Geometry.BoundsR.theta_bounds
theorem h_interval : 793/1000<h ∧ h<803/1000 := QRH.Record1252270103Return.Geometry.BoundsR.h_interval
theorem ly_coarse : 458/1000<ly ∧ ly<467/1000 := QRH.Record1252270103Return.Geometry.BoundsR.ly_coarse
theorem length_sum : lx+ly=1-ell := Arithmetic.x_add_y
theorem row_endpoint : h=1-lx+ell := Assembly.row_endpoint
theorem small_saving : 7/100<ly/2-h*(17/50-1/6)-1/50 := QRH.Record1252270103Return.Geometry.BoundsR.small_saving
theorem signalShift_eq : -(4+b)/6=Assembly.signalShift := Assembly.signalShift_eq.symm
theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ≤1/10000000000) : h+ζ≤Arithmetic.dPlus := by
 rw [Arithmetic.dPlus_eq];linarith
end
end RepeatedMarksReturn.Transport.Transport

namespace QRH.RepeatedMarks.Return.GenericPhysical.Assembly
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
abbrev signalShift : ℝ := RepeatedMarksReturn.Transport.Assembly.signalShift
abbrev signal := RepeatedMarksReturn.Transport.Assembly.signal
end
end QRH.RepeatedMarks.Return.GenericPhysical.Assembly
