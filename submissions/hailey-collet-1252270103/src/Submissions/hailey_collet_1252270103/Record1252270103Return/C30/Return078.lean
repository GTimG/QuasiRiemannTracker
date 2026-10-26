/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row078_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10781781363937024984852/1296268541015625:ℝ), (276786481832118054511796/11666416869140625:ℝ), (262852891679595415842688/11666416869140625:ℝ), (16620488424582117238912/2333283373828125:ℝ)],
![(20673578088103578194114/1296268541015625:ℝ), (528746311840595669807314/11666416869140625:ℝ), (20003932848618209746688/466656674765625:ℝ), (157414212167791777606912/11666416869140625:ℝ)],
![(39928954337880711032173/5185074164062500:ℝ), (1017533629586970174992597/46665667476562500:ℝ), (239650806244245118909312/11666416869140625:ℝ), (75107546107734174983552/11666416869140625:ℝ)]]
theorem row078_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (586777703966673242059/173982218452992000000000:ℝ) row078_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row078_coefficients,Fin.sum_univ_succ]
 ring
theorem row078_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row078_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_coefficients]
#print axioms row078_identity
#print axioms row078_pos
end
end Record1252270103Return.C30
