import QRH.NumericFacts
import QRH.Detector.OptimizedData

namespace OAI
noncomputable section
namespace SevenEighths.QRHParameters
open Parameters

lemma optimized_transport_budgets {gap:ℝ} (D:HighData gap)
    (ht:D.t<(1/10000000000000000:ℝ))
    (he:2000*D.e≤D.t) (heps:((D.N:ℝ)+8)*D.eps≤D.t):
    D.sigma/8+8*D.e+D.sigma/16+1/200≤QRH.ly/2-(13/75)*QRH.h-1/50 ∧
    D.sigma/8+D.sigma/16≤1/3000 ∧
    D.sigma/8+D.e≤(87/100)*(D.rmin/2) ∧
    D.sigma/8+D.sigma/16≤1+QRH.C QRH.theta ∧
    2*QRH.zeta+26*D.e+(D.N+8)*D.eps+D.t+D.t*QRH.ell+D.sigma/16+D.sigma/8≤1/200 ∧
    QRH.h+QRH.zeta≤7/8-D.t := by
  have hgeo : (7/100:ℝ)≤QRH.ly/2-(13/75)*QRH.h-1/50 := by
    norm_num [QRH.ly,QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hC : 0≤QRH.C QRH.theta := by
    norm_num [QRH.C,QRH.ly,QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hcap := QRH.NumericFacts.h_zeta_upper
  have hell : QRH.ell≤1 := by norm_num [QRH.ell,QRH.theta]
  have htel := mul_le_mul_of_nonneg_left hell D.t_pos.le
  have hs : D.sigma≤D.t := by linarith [D.high_saving,D.t_pos]
  have hemin : D.e≤D.rmin/100 := by
    have hrt := mul_le_mul_of_nonneg_left (show D.t≤1 by linarith [D.t_small]) D.rmin_pos.le
    nlinarith [D.epsilon_gap,D.detector_budget,D.kappa_pos,D.cost_pos]
  refine ⟨by linarith,by linarith,?_,by linarith,?_,by linarith⟩
  · nlinarith [D.window_budget,D.e_pos]
  · norm_num [QRH.zeta]
    linarith

end SevenEighths.QRHParameters
end
end OAI
