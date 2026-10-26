/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row075_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2337955262737554136797961/162033375785888671875:ℝ), (6291883676796085111568831/162033375785888671875:ℝ), (5640517582038592265351729/162033375785888671875:ℝ), (1686589167980061290580859/162033375785888671875:ℝ)],
![(1605192612566301463945453/64813350314355468750:ℝ), (2318655886537048903160321/36007416841308593750:ℝ), (8983244876401415835879754/162033375785888671875:ℝ), (2562274918400449431521942/162033375785888671875:ℝ)],
![(19879016818054530827500321/1728356008382812500000:ℝ), (150118481287277502273886307/5185068025148437500000:ℝ), (155025220303399784378309/6481335031435546875:ℝ), (1048085794050184928476933/162033375785888671875:ℝ)]]
theorem row075_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1048085794050184928476933/302052104974336000000000000:ℝ) row075_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row075_coefficients,Fin.sum_univ_succ]
 ring
theorem row075_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row075_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_coefficients]
#print axioms row075_identity
#print axioms row075_pos
end
end Record1252270103Finite
