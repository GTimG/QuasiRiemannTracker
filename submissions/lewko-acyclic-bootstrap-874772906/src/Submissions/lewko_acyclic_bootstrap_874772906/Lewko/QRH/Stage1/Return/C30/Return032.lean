/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row032_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1461914156139562593169381594410287092/657878329670079693392578125:ℝ), (4342211656443742962155897223862959604/657878329670079693392578125:ℝ), (1432954171601991548445652921589868544/219292776556693231130859375:ℝ), (94570986171034237629685167354462208/43858555311338646226171875:ℝ)],
![(2816068861443765416539036192092601232/657878329670079693392578125:ℝ), (1672410297147599367172664251119766096/131575665934015938678515625:ℝ), (8276261661044362290965964339286360064/657878329670079693392578125:ℝ), (2730278582051409413104266775780130816/657878329670079693392578125:ℝ)],
![(271023026165629012434255273645816848/131575665934015938678515625:ℝ), (4022722086940336953763371414110544976/657878329670079693392578125:ℝ), (3980282324037787535545939246100652032/657878329670079693392578125:ℝ), (1312675135031128555434681700219191296/657878329670079693392578125:ℝ)]]
theorem row032_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (40059665986057389997396292120947/306593523294281548701696000000000:ℝ) row032_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row032_coefficients,Fin.sum_univ_succ]
 ring
theorem row032_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row032_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_coefficients]
#print axioms row032_identity
#print axioms row032_pos
end
end LewkoStage1Return.C30
