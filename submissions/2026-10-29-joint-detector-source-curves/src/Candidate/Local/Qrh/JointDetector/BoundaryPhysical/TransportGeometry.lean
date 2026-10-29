/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module TransportGeometry (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.IntermediateGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.TransportGeometry
set_option autoImplicit false
namespace Qrh.JointDetector.BoundaryPhysical.Return.Geometry
noncomputable abbrev dPlus [QRH.Record1252270103Return.Geometry.Parameters] : ℝ :=
  QRH.Record1252270103Return.Geometry.h+1/10000000000000000000000
noncomputable section
open QRH.Record1252270103Return.Geometry
variable [Parameters]
/-- PR76's coarse box `BoundsR`, widened at the lower end of `theta` (`874/1000 → 873/1000`) and at
the upper ends of `h` (`803/1000 → 806/1000`) and `ell` (`1690/10000 → 171/1000`), so that it holds at
`theta = 174799/200000`, `h = 8053/10000`. The two functional fields are unchanged. -/
class BoundsN : Prop where
 theta_bounds : 873/1000<QRH.Record1252270103Return.Geometry.theta ∧ QRH.Record1252270103Return.Geometry.theta<7/8
 h_interval : 793/1000<QRH.Record1252270103Return.Geometry.h ∧ QRH.Record1252270103Return.Geometry.h<813/1000
 ly_coarse : 458/1000<QRH.Record1252270103Return.Geometry.y ∧ QRH.Record1252270103Return.Geometry.y<473/1000
 ell_interval : 1672/10000<QRH.Record1252270103Return.Geometry.ell ∧ QRH.Record1252270103Return.Geometry.ell<173/1000
 small_saving : 7/100<QRH.Record1252270103Return.Geometry.y/2-QRH.Record1252270103Return.Geometry.h*(17/50-1/6)-1/50
 floor_margin : 4/25*QRH.Record1252270103Return.Geometry.x-3/20-51/100*QRH.Record1252270103Return.Geometry.y+67/100*Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus-3/20*QRH.Record1252270103Return.Geometry.ell ≤ QRH.Record1252270103Return.Geometry.signal QRH.Record1252270103Return.Geometry.theta-1/10000
end
end Qrh.JointDetector.BoundaryPhysical.Return.Geometry

namespace Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic
noncomputable section
open QRH.Record1252270103Return
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
abbrev theta : ℝ := Geometry.theta
abbrev ell : ℝ := Geometry.ell
abbrev x : ℝ := Geometry.x
abbrev y : ℝ := Geometry.y
abbrev h : ℝ := Geometry.h
abbrev dPlus : ℝ := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus
theorem ell_eq : ell=11/3-4*theta := by
 have hs := Geometry.signal_at_boundary
 dsimp [Geometry.signal,Geometry.signalShift] at hs
 linarith [Geometry.x_add_y]
theorem x_eq : x=1+ell-h := by dsimp [h,Geometry.h];ring
theorem y_eq : y=h-2*ell := by dsimp [h,Geometry.h];linarith [Geometry.x_add_y]
theorem dPlus_eq : dPlus=h+1/10000000000000000000000 := rfl
theorem ell_pos : 0<ell := Geometry.ell_pos
theorem ell_lt_x : ell<x := Geometry.ell_lt_x
theorem x_lt_y : x<y := Geometry.x_lt_y
theorem y_lt_two_x : y<2*x := by
 have hg : 0<2*x-y-ell := Geometry.Parameters.dilation_gap
 have he : 0<ell := Geometry.ell_pos
 linarith
theorem y_lt_half : y<1/2 := Geometry.y_lt_half
theorem half_lt_h : 1/2<h := by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval]
theorem h_lt_two_y : h<2*y := by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval,Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ly_coarse]
theorem sixth_lt_ell : 1/6<ell := Geometry.sixth_lt_ell
theorem ell_lt_fifth : ell<1/5 := Geometry.ell_lt_fifth
theorem four_ell_lt_h : 4*ell<h := by
 have hh : 793/1000<h := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval.1
 have he : ell<173/1000 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ell_interval.2
 linarith
theorem x_add_y : x+y=1-ell := Geometry.x_add_y
theorem h_lt_dPlus : h<dPlus := by dsimp [dPlus,Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus];linarith
theorem dPlus_lt_one : dPlus<1 := by dsimp [dPlus,Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus];linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval]
end
end Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic
namespace Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
 unfold signalShift
 linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
 unfold signal signalShift
 linarith [ell_eq,x_add_y]
theorem theta_lt_seven_eighths : theta<7/8 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.2
theorem theta_gt_half : 1/2<theta := by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.1]
theorem row_endpoint : h=1-x+ell := by linarith [x_eq]
end
end Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly
namespace Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000000000000000
theorem ell_interval : 1672/10000<ell ∧ ell<173/1000 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ell_interval
theorem h_pos : 0<h := by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval.1]
theorem extended_h_lt_one : h+rowExtension<1 := by dsimp [rowExtension];linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval.2]
theorem theta_lower : 873/1000<theta := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds.1
theorem theta_bounds : 873/1000<theta ∧ theta<7/8 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.theta_bounds
theorem h_interval : 793/1000<h ∧ h<813/1000 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval
theorem ly_coarse : 458/1000<ly ∧ ly<473/1000 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ly_coarse
theorem length_sum : lx+ly=1-ell := Arithmetic.x_add_y
theorem row_endpoint : h=1-lx+ell := Assembly.row_endpoint
theorem small_saving : 7/100<ly/2-h*(17/50-1/6)-1/50 := Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.small_saving
theorem signalShift_eq : -(4+b)/6=Assembly.signalShift := Assembly.signalShift_eq.symm
theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ≤1/10000000000000000000000) : h+ζ≤Arithmetic.dPlus := by
 rw [Arithmetic.dPlus_eq];linarith
end
end Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport

namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
abbrev signalShift : ℝ := Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift
abbrev signal := Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signal
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
