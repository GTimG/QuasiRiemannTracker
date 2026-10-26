import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Geometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Transport
noncomputable section

abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
/-- The tolerance of the row length in the transport: the offset of the extended row. -/
def rowExtension : ℝ := Arithmetic.dPlusOffset

theorem rowExtension_pos : 0 < rowExtension := Arithmetic.dPlusOffset_pos

theorem ell_interval : (1 : ℝ)/6 < ell ∧ ell < 1/5 :=
  ⟨Arithmetic.sixth_lt_ell, Arithmetic.ell_lt_fifth⟩
theorem h_pos : 0 < h := by
  have hh := Arithmetic.h_bounds
  change 0 < Arithmetic.h
  linarith [hh.1]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  have hh := Arithmetic.h_bounds
  have hz := Arithmetic.dPlusOffset_bounds
  change Arithmetic.h+rowExtension < 1
  unfold rowExtension
  linarith [hh.2, hz.2]

theorem theta_lower : (874 : ℝ)/1000 < theta := by norm_num [theta, Arithmetic.theta]
theorem theta_bounds : (874 : ℝ)/1000 < theta ∧ theta < 7/8 :=
  ⟨theta_lower, Assembly.theta_lt_seven_eighths⟩
bracket h_interval (digits := 9) : h using [Arithmetic.h_bounds] unfolding [h]
bracket ly_coarse (digits := 9) : ly using [Arithmetic.h_bounds]
  unfolding [ly, Arithmetic.y, Arithmetic.ell, Arithmetic.theta]
theorem length_sum : lx+ly = 1-ell := Arithmetic.x_add_y
theorem row_endpoint : h = 1-lx+ell := Assembly.row_endpoint
theorem small_saving : (7/100 : ℝ) < ly/2-h*(17/50-1/6)-1/50 := by
  have hh := Arithmetic.h_bounds
  change (7/100 : ℝ) < Arithmetic.y/2-Arithmetic.h*(17/50-1/6)-1/50
  unfold Arithmetic.y
  norm_num [Arithmetic.ell, Arithmetic.theta]
  linarith [hh.1, hh.2]
theorem signalShift_eq : -(4+b)/6 = Assembly.signalShift := by
  exact Assembly.signalShift_eq.symm

end
end Cycle63.Transport

end Record1252270103Bootstrap.PR67
