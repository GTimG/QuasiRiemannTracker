/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row079_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19278478654077907250783879707/324066751571777343750:ℝ), (11232060252858650409895003967/64813350314355468750:ℝ), (36338463304922139767407166791/216044501047851562500:ℝ), (11750581564778576568279740039/216044501047851562500:ℝ)],
![(18591745561146926685938335097/162033375785888671875:ℝ), (54053672716152134887399877111/162033375785888671875:ℝ), (52355097086297507931908061856/162033375785888671875:ℝ), (16893169931292299730446519842/162033375785888671875:ℝ)],
![(6028601528179263829260786079/108022250523925781250:ℝ), (17495792299646024631903271829/108022250523925781250:ℝ), (50740796733975353454185429213/324066751571777343750:ℝ), (16339224419575071046257971963/324066751571777343750:ℝ)]]
theorem row079_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (16339224419575071046257971963/4948821687899521024000000000000:ℝ) row079_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row079_coefficients,Fin.sum_univ_succ]
 ring
theorem row079_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row079_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_coefficients]
#print axioms row079_identity
#print axioms row079_pos
end
end Record1252270103Finite
