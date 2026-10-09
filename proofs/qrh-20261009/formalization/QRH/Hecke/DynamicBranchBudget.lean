import OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget
import QRH.Hecke.DynamicCountOptimization
/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Dynamic plain capacity with actual inverse/plain detector witnesses and physical coefficients. -/
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount


theorem plain_marked_loss_optimized (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(6*QRH.kappa0+12*Δ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(6*QRH.kappa0+12*Δ)+commonLoss ε εm mesh ν  := by
  have hk0 : (13/18:ℝ) ≤ QRH.kappa0 := by norm_num [QRH.kappa0, QRH.theta]

  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(6*QRH.kappa0+12*Δ)-ν)=
      2*(δ*x)*(1-2*m)/(6*QRH.kappa0+12*Δ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith


theorem plain_requested_capacity_optimized (Δ x t r m ε ν : ℝ)
    (hΔ : 0≤Δ) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤QRHDetectorRowCount.crossing x t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*QRH.kappa0+12*Δ)) :
    0≤(1-2*m)/(6*QRH.kappa0+12*Δ)-ν ∧ (1-2*m)/(6*QRH.kappa0+12*Δ)-ν≤7/37 ∧
      2*m+6*(QRH.kappa0+2*Δ)*((1-2*m)/(6*QRH.kappa0+12*Δ)-ν)≤1  := by
  have hk0 : (13/18:ℝ) ≤ QRH.kappa0 := by norm_num [QRH.kappa0, QRH.theta]

  have hcross := QRHDetectorRowCount.crossing_bounds hx hx1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<6*QRH.kappa0+12*Δ := by linarith
  have hc : (1-2*m)/(6*QRH.kappa0+12*Δ)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  have heq : 6*(QRH.kappa0+2*Δ)=6*QRH.kappa0+12*Δ := by ring
  rw [heq,mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.HeckeDetectorBranchBudget
end
end OAI
