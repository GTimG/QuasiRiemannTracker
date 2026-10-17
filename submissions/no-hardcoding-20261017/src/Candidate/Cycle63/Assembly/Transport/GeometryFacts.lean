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
theorem h_interval : (793 : ℝ)/1000 < h ∧ h < 797/1000 := by
  have hh := Arithmetic.h_bounds
  change (793 : ℝ)/1000 < Arithmetic.h ∧ Arithmetic.h < 797/1000
  constructor <;> linarith [hh.1, hh.2]
theorem ly_coarse : (458 : ℝ)/1000 < ly ∧ ly < 462/1000 := by
  have hh := Arithmetic.h_bounds
  change (458 : ℝ)/1000 < Arithmetic.y ∧ Arithmetic.y < 462/1000
  unfold Arithmetic.y
  norm_num [Arithmetic.ell, Arithmetic.theta]
  constructor <;> linarith [hh.1, hh.2]
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

theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ ≤ rowExtension) :
    h+ζ ≤ Arithmetic.dPlus := by
  rw [Arithmetic.dPlus_eq]
  have he : rowExtension = Arithmetic.dPlusOffset := rfl
  linarith

theorem principal_w_reserve : 0 < ly/20-(1+h)/1000-1/4000 :=
  Arithmetic.principal_y_reserve

theorem principal_z_reserve : 0 < h/600-1/1000-1/4000 :=
  Arithmetic.principal_h_reserve

end
end Cycle63.Transport
