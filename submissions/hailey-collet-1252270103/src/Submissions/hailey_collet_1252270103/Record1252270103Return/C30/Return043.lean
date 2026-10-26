/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1199088727400573244781300831/5929071855468750000:ℝ), (5933686298105898125135895433/9881786425781250000:ℝ), (122337231440934476161337314/205870550537109375:ℝ), (363184129386233525983211942/1852834954833984375:ℝ)],
![(7756056832612002714460581013/19763572851562500000:ℝ), (69063449332566239766538887359/59290718554687500000:ℝ), (427034675117591167879178228/370566990966796875:ℝ), (46938060800175740078148692/123522330322265625:ℝ)],
![(90277986813224042759535415603/474325748437500000000:ℝ), (53573974865532259966988119511/94865149687500000000:ℝ), (1034838625956179237031552238/1852834954833984375:ℝ), (341120315352908701580750746/1852834954833984375:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (170560157676454350790375373/1768414563532800000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ]
 ring
theorem row043_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
#print axioms row043_identity
#print axioms row043_pos
end
end Record1252270103Return.C30
