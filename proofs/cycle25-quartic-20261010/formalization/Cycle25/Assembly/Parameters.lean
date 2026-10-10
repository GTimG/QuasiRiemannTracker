import Cycle25.Arithmetic.Geometry

/-! Physical geometry at the exact Cycle25 algebraic boundary. -/
noncomputable section
namespace Cycle25

def theta : ℝ := Arithmetic.b0
def ell : ℝ := Arithmetic.ell0
def lx : ℝ := Arithmetic.x0
def ly : ℝ := Arithmetic.y0
def h : ℝ := Arithmetic.h0
def b : ℝ := ly-lx
def rowExtension : ℝ := 1/1000000
def signal (s : ℝ) : ℝ := s-(4+b)/6

theorem ell_interval : (16712:ℝ)/100000 < ell ∧ ell < 167121/1000000 :=
  Arithmetic.ell0_short_interval
theorem h_interval : (793:ℝ)/1000 < h ∧ h < 795/1000 := Arithmetic.h0_interval
theorem theta_eq : theta = 11/12-ell/4 := rfl
theorem theta_pos : 0 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_gt_half : (1:ℝ)/2 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_lt_seven_eighths : theta < (7:ℝ)/8 := by rw [theta_eq]; linarith [ell_interval.1]
theorem theta_lt_one : theta < 1 := theta_lt_seven_eighths.trans (by norm_num)
theorem length_sum : lx+ly = 1-ell := by unfold lx ly ell Arithmetic.x0 Arithmetic.y0; ring
theorem length_difference : ly-lx=b := rfl
theorem row_endpoint : h=1-lx+ell := by unfold h lx ell Arithmetic.x0; ring
theorem y_endpoint : ly=h-2*ell := rfl
theorem signal_low : signal theta=lx/2+b/12 := by
  rw [signal,theta_eq]
  have := length_sum
  unfold b
  linarith
theorem signal_slope (s t : ℝ) : signal s-signal t=s-t := by unfold signal; ring
theorem ell_pos : 0 < ell := by linarith [ell_interval.1]
theorem ell_lt_one_fifth : ell < (1:ℝ)/5 := by linarith [ell_interval.2]
theorem x_rescaled_pos : 0 < lx-ell := sub_pos.mpr Arithmetic.physical_geometry.1
theorem b_pos : 0 < b := sub_pos.mpr Arithmetic.physical_geometry.2.1
theorem ly_lt_half : ly < (1:ℝ)/2 := Arithmetic.physical_geometry.2.2.2.1
theorem ly_coarse : (458:ℝ)/1000 < ly ∧ ly < 461/1000 := by
  rw [y_endpoint]
  constructor <;> linarith [h_interval.1,h_interval.2,ell_interval.1,ell_interval.2]
theorem y_rescaled_pos : 0 < ly-ell := by linarith [ly_coarse.1,ell_interval.2]
theorem row_rescaled_pos : 0 < 1-3*ell := by linarith [ell_interval.2]
theorem gram_domination : 0 < ly-ell-(11:ℝ)/6*b := by
  have := length_sum
  unfold b
  linarith [ly_coarse.2,ell_interval.2]
theorem h_pos : 0 < h := by linarith [h_interval.1]
theorem h_gt_half : (1:ℝ)/2 < h := by linarith [h_interval.1]
theorem h_lt_one : h < 1 := by linarith [h_interval.2]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem extended_row_count_supply : (7:ℝ)/37 < ell/(h+rowExtension) := by
  apply (lt_div_iff₀ (add_pos h_pos rowExtension_pos)).2
  norm_num [rowExtension]
  linarith [ell_interval.1,h_interval.2]
theorem row_count_supply : (7:ℝ)/37 < ell/h := by
  apply (lt_div_iff₀ h_pos).2
  linarith [ell_interval.1,h_interval.2]
theorem row_extension_supply : h < 5*ell := by linarith [h_interval.2,ell_interval.1]
theorem numerator_short : h < 2*ly := Arithmetic.physical_geometry.2.2.2.2.2
theorem extended_numerator_short : h+rowExtension < 2*ly := by
  rw [y_endpoint]
  norm_num [rowExtension]
  linarith [h_interval.1,ell_interval.2]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  norm_num [rowExtension]
  linarith [h_interval.2]
theorem extended_row_supply : h+rowExtension < 5*ell := by
  norm_num [rowExtension]
  linarith [h_interval.2,ell_interval.1]
theorem numerator_supply_all {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1:ℝ)/2 ≤ d) :
    (2*ly-d)/(6*kap) < ell := by
  apply (div_lt_iff₀ (by linarith : 0 < 6*kap)).2
  have hprod := mul_le_mul_of_nonneg_left hk ell_pos.le
  nlinarith [ly_coarse.2,ell_interval.1]
theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (5*ell-1+v)/8 ≤ 0 := by
  have hm : max 0 (5*ell-1+v) ≤ 8*v := max_le (by linarith) (by linarith [ell_lt_one_fifth])
  linarith
theorem low_rescaled_identity (v : ℝ) :
    (1-ell-2*v)+(ell-v)-1 = -3*v := by ring
theorem small_row_margin : h*(17/50-1/6)-ly/2+(63:ℝ)/5000 < 0 := by
  dsimp only [h,ly]
  linarith [Arithmetic.small_row_margin]
theorem principal_w_margin : 0 < ly/20 := by linarith [ly_coarse.1]
theorem principal_z_margin : 0 < h/600 := by linarith [h_pos]

end Cycle25
