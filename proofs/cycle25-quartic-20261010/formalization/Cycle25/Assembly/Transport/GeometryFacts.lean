import Cycle25.Assembly.Parameters
namespace Cycle25.Transport
lemma theta_lower : (874:ℝ)/1000 < Cycle25.theta := by
  rw [Cycle25.theta_eq]
  linarith [Cycle25.ell_interval]
lemma theta_bounds : (874:ℝ)/1000 < Cycle25.theta ∧ Cycle25.theta < 7/8 :=
  ⟨theta_lower, Cycle25.theta_lt_seven_eighths⟩
lemma small_saving : (7/100:ℝ) < Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50 := by
  linarith [Cycle25.ly_coarse, Cycle25.h_interval]
end Cycle25.Transport
