/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Honest transport guards for the new parameters. The original Geometry.Parameters
and all arithmetic meanings are retained. This is not the old Bounds instance.

-/
import Candidate.Feedback.FourthPower.Parameters
import Submissions.hailey_collet_1252270103.Record1252270103Return.TransportGeometry

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower
open QRH.Record1252270103Return
noncomputable section
class TransportBounds [Geometry.Parameters] : Prop where
  theta_bounds : 874/1000 < Geometry.theta ∧ Geometry.theta < 7/8
  h_interval : 793/1000 < Geometry.h ∧ Geometry.h < 802/1000
  ly_coarse : 458/1000 < Geometry.y ∧ Geometry.y < 466/1000
  ell_interval : 1672/10000 < Geometry.ell ∧ Geometry.ell < 169/1000
  small_saving : 7/100 < Geometry.y/2-Geometry.h*(17/50-1/6)-1/50
  floor_margin : 4/25*Geometry.x-3/20-51/100*Geometry.y+
    67/100*Geometry.dPlus-3/20*Geometry.ell ≤ Geometry.signal Geometry.theta-1/200

namespace TransportBounds
/-- All fields are proved for our actual rational data, not assumed. -/
theorem of_exact_values [Geometry.Parameters]
    (ht : Geometry.theta = Candidate.Feedback.FourthPower.theta)
    (he : Geometry.ell = Candidate.Feedback.FourthPower.ell)
    (hx : Geometry.x = Candidate.Feedback.FourthPower.x)
    (hy : Geometry.y = Candidate.Feedback.FourthPower.y) : TransportBounds := by
  constructor <;>
    norm_num [Geometry.h, Geometry.dPlus, Geometry.signal, Geometry.signalShift,
      ht, he, hx, hy, Candidate.Feedback.FourthPower.theta, Candidate.Feedback.FourthPower.ell,
      Candidate.Feedback.FourthPower.x, Candidate.Feedback.FourthPower.y, Candidate.Feedback.FourthPower.h]
end TransportBounds
end
end Candidate.Feedback.FourthPower

namespace RunboLiFeedbackTransport.Arithmetic
noncomputable section
open QRH.Record1252270103Return
variable [Geometry.Parameters] [Candidate.Feedback.FourthPower.TransportBounds]
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
theorem half_lt_h : 1/2<h := by linarith [Candidate.Feedback.FourthPower.TransportBounds.h_interval]
theorem h_lt_two_y : h<2*y := by linarith [Candidate.Feedback.FourthPower.TransportBounds.h_interval,Candidate.Feedback.FourthPower.TransportBounds.ly_coarse]
theorem sixth_lt_ell : 1/6<ell := Geometry.sixth_lt_ell
theorem ell_lt_fifth : ell<1/5 := Geometry.ell_lt_fifth
theorem four_ell_lt_h : 4*ell<h := by
 have hh : 793/1000<h := Candidate.Feedback.FourthPower.TransportBounds.h_interval.1
 have he : ell<169/1000 := Candidate.Feedback.FourthPower.TransportBounds.ell_interval.2
 linarith
theorem x_add_y : x+y=1-ell := Geometry.x_add_y
theorem h_lt_dPlus : h<dPlus := by dsimp [dPlus,Geometry.dPlus];linarith
theorem dPlus_lt_one : dPlus<1 := by dsimp [dPlus,Geometry.dPlus];linarith [Candidate.Feedback.FourthPower.TransportBounds.h_interval]
end
end RunboLiFeedbackTransport.Arithmetic
namespace RunboLiFeedbackTransport.Assembly
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.Feedback.FourthPower.TransportBounds]
open RunboLiFeedbackTransport.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
 unfold signalShift
 linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
 unfold signal signalShift
 linarith [ell_eq,x_add_y]
theorem theta_lt_seven_eighths : theta<7/8 := Candidate.Feedback.FourthPower.TransportBounds.theta_bounds.2
theorem theta_gt_half : 1/2<theta := by linarith [Candidate.Feedback.FourthPower.TransportBounds.theta_bounds.1]
theorem row_endpoint : h=1-x+ell := by linarith [x_eq]
end
end RunboLiFeedbackTransport.Assembly
namespace RunboLiFeedbackTransport.Transport
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.Feedback.FourthPower.TransportBounds]
abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000
theorem ell_interval : 1672/10000<ell ∧ ell<169/1000 := Candidate.Feedback.FourthPower.TransportBounds.ell_interval
theorem h_pos : 0<h := by linarith [Candidate.Feedback.FourthPower.TransportBounds.h_interval.1]
theorem extended_h_lt_one : h+rowExtension<1 := by dsimp [rowExtension];linarith [Candidate.Feedback.FourthPower.TransportBounds.h_interval.2]
theorem theta_lower : 874/1000<theta := Candidate.Feedback.FourthPower.TransportBounds.theta_bounds.1
theorem theta_bounds : 874/1000<theta ∧ theta<7/8 := Candidate.Feedback.FourthPower.TransportBounds.theta_bounds
theorem h_interval : 793/1000<h ∧ h<802/1000 := Candidate.Feedback.FourthPower.TransportBounds.h_interval
theorem ly_coarse : 458/1000<ly ∧ ly<466/1000 := Candidate.Feedback.FourthPower.TransportBounds.ly_coarse
theorem length_sum : lx+ly=1-ell := Arithmetic.x_add_y
theorem row_endpoint : h=1-lx+ell := Assembly.row_endpoint
theorem small_saving : 7/100<ly/2-h*(17/50-1/6)-1/50 := Candidate.Feedback.FourthPower.TransportBounds.small_saving
theorem signalShift_eq : -(4+b)/6=Assembly.signalShift := Assembly.signalShift_eq.symm
theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ≤1/10000000000) : h+ζ≤Arithmetic.dPlus := by
 rw [Arithmetic.dPlus_eq];linarith
end
end RunboLiFeedbackTransport.Transport
