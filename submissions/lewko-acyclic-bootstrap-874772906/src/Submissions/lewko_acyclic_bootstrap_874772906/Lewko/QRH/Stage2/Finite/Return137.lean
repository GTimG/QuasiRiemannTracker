/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row137_coefficients : Fin 3 → Fin 4 → ℝ := ![![(209975286652368576462054490976933909698/5615091600184199864368599609375:ℝ),(601064845322318182739297535139974969538/5615091600184199864368599609375:ℝ),(572686561288228097626116487710167719424/5615091600184199864368599609375:ℝ),(181595251305617404172258727922126659584/5615091600184199864368599609375:ℝ)],
![(415772329904254212416118579761910274664/5615091600184199864368599609375:ℝ),(1188312385355839025548373961778110663272/5615091600184199864368599609375:ℝ),(226058998824921528999577824874110752768/1123018320036839972873719921875:ℝ),(357751350617814750820862129854353375232/5615091600184199864368599609375:ℝ)],
![(208072665011658555096513811305335856712/5615091600184199864368599609375:ℝ),(118807307085348909884693746180774244264/1123018320036839972873719921875:ℝ),(564359801709537645273049558085352077312/5615091600184199864368599609375:ℝ),(178394093510076780167065275986816712704/5615091600184199864368599609375:ℝ)]]
theorem row137_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (10888311371464647226993730223804731/5233644702004220050649038848000000000:ℝ) row137_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row137_coefficients,Fin.sum_univ_succ]
 ring
theorem row137_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row137_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row137_coefficients]
#print axioms row137_identity
#print axioms row137_pos
end
end LewkoStage2Finite
