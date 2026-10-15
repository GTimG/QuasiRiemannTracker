import Candidate.Cycle63.Assembly.Geometry

namespace Cycle63.Transport
noncomputable section

abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000

theorem ell_interval : (1672 : ℝ)/10000 < ell ∧ ell < 16725/100000 := by norm_num [ell, Arithmetic.ell]
theorem h_pos : 0 < h := by norm_num [h, Arithmetic.h]
theorem extended_h_lt_one : h+rowExtension < 1 := by norm_num [h, Arithmetic.h, rowExtension]

theorem theta_lower : (874 : ℝ)/1000 < theta := by norm_num [theta, Arithmetic.theta]
theorem theta_bounds : (874 : ℝ)/1000 < theta ∧ theta < 7/8 :=
  ⟨theta_lower, Assembly.theta_lt_seven_eighths⟩
theorem h_interval : (793 : ℝ)/1000 < h ∧ h < 796/1000 := by norm_num [h, Arithmetic.h]
theorem ly_coarse : (458 : ℝ)/1000 < ly ∧ ly < 461/1000 := by norm_num [ly, Arithmetic.y]
theorem length_sum : lx+ly = 1-ell := Arithmetic.x_add_y
theorem row_endpoint : h = 1-lx+ell := Assembly.row_endpoint
theorem small_saving : (7/100 : ℝ) < ly/2-h*(17/50-1/6)-1/50 := by
  norm_num [ly, h, Arithmetic.y, Arithmetic.h]
theorem signalShift_eq : -(4+b)/6 = Assembly.signalShift := by
  exact Assembly.signalShift_eq.symm

theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ ≤ 1/10000000000) :
    h+ζ ≤ Arithmetic.dPlus := by
  rw [Arithmetic.dPlus_eq]
  linarith

theorem principal_w_reserve :
    ly/20-(1+h)/1000-1/4000 = 629887819/30000000000 :=
  Arithmetic.principal_y_reserve

theorem principal_z_reserve :
    h/600-1/1000-1/4000 = 151059/2000000000 :=
  Arithmetic.principal_h_reserve

end
end Cycle63.Transport
