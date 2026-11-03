import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedHighData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedCentralExponent

/- Actual rational contour budgets for the existing parameter record.
   Use half its positive saving; the boundary and physical probe are unchanged. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section

theorem rational_geometric_budget {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    D.sigma/2+8*D.e+D.t/8≤1/16 := by
  have hdet := D.detector_budget
  have hk := D.kappa_pos
  have hc := D.cost_pos
  have he := D.epsilon_small
  have hs := D.high_saving
  have ht := D.t_small
  linarith [D.t_pos]

theorem rational_principal_budget {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    D.sigma/2+D.t/8≤1/3000 := by
  linarith [D.high_saving,D.t_small,D.t_pos]

theorem rational_window_budget {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    D.sigma/2+D.e≤(13/15)*((7/8)*D.rmin) := by
  have hdet := D.detector_budget
  have hk := D.kappa_pos
  have hc := D.cost_pos
  have hr := D.rmin_pos
  have ht := D.t_small
  have hsmall : D.rmin*D.t≤D.rmin := by nlinarith
  have heps := D.epsilon_gap
  have he : 576*D.e≤D.rmin := by linarith
  linarith [D.window_budget]

theorem rational_floor_budget {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    2*D.t+26*D.e+(D.N+8)*D.eps+D.t+D.t/5+D.t/8+D.sigma/2≤7/1200 := by
  have hb := D.central_budget 0 (by norm_num) (by norm_num)
  have hs := D.high_saving
  linarith [D.t_pos]

theorem rational_central_budget {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    hRat*(159*D.ε+D.t+D.t+7*D.t)+2*D.t+(3/2)*(2*D.t)+
      (26*D.e+(D.N+8)*D.eps+D.t+D.t/5)+(D.t+D.t+D.t)+D.t≤1/1000000000000000 := by
  have hb := D.central_budget 1 (by norm_num) (by norm_num)
  have hh : hRat≤(9/10:ℝ) := by norm_num [hRat,ellRat,bRat]
  have hε := D.epsilon_pos
  have ht := D.t_pos
  have hnonneg : 0≤159*D.ε+D.t+D.t+7*D.t := by positivity
  have hw := mul_le_mul_of_nonneg_right hh hnonneg
  linarith [D.epsilon_pos,D.t_pos]

theorem rational_high_saving {Δ mesh : ℝ}
    (D : RetunedHighData Δ ellRat (1/1000000000000000) mesh) :
    D.sigma/2+D.t/8+D.t/8≤D.t := by
  linarith [D.high_saving,D.sigma_pos]

#print axioms rational_geometric_budget
#print axioms rational_principal_budget
#print axioms rational_window_budget
#print axioms rational_floor_budget
#print axioms rational_central_budget
#print axioms rational_high_saving
end
end BelowSevenEighthsTight.Parameters
