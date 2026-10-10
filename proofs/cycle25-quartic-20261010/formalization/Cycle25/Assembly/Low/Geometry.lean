import Cycle25.Assembly.Parameters

namespace Cycle25.LowGeometry

theorem theta_coarse : (874:ℝ)/1000 < Cycle25.theta := by
  rw [Cycle25.theta_eq]
  linarith [Cycle25.ell_interval.2]

theorem x_pos : 0 < Cycle25.lx := by
  linarith [Cycle25.x_rescaled_pos,Cycle25.ell_pos]

theorem signal_pos : 0 < Cycle25.signal Cycle25.theta := by
  rw [Cycle25.signal_low]
  linarith [x_pos,Cycle25.b_pos]

theorem scale_square : (2*Cycle25.lx-Cycle25.ly)+Cycle25.ly=2*Cycle25.lx := by ring

theorem gram_power (δ : ℝ) :
    Cycle25.lx+Cycle25.b*(1/6)+Cycle25.ly*δ =
      2*Cycle25.signal Cycle25.theta+Cycle25.ly*δ := by
  rw [Cycle25.signal_low]
  ring

theorem gram_sqrt_power (δ : ℝ) :
    (2*Cycle25.signal Cycle25.theta+Cycle25.ly*δ)*(1/2) =
      Cycle25.signal Cycle25.theta+(Cycle25.ly/2)*δ := by ring

theorem dilation_gap : 0 < 2*Cycle25.lx-Cycle25.ly-Cycle25.ell := by
  linarith [Cycle25.length_sum,Cycle25.ly_coarse.2,Cycle25.ell_interval.2]

theorem dilation_le_y : 2*Cycle25.lx-Cycle25.ly ≤ Cycle25.ly := by
  linarith [Cycle25.b_pos,Cycle25.length_difference]

end Cycle25.LowGeometry
