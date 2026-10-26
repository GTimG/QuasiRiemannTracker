/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row224_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10129592936359848511760564539519/239533516085293116482793750000:ℝ),(2293519786815153495529779893674093/32337024671514570725177156250000:ℝ),(518290151535664230917346496431859/16168512335757285362588578125000:ℝ),(7131580474142366096971518702469/3233702467151457072517715625000:ℝ)],
![(4679080958967766624132403062537/35930027412793967472419062500:ℝ),(1923875358397500354502312242796649/8084256167878642681294289062500:ℝ),(1050718877541927158414151784841371/8084256167878642681294289062500:ℝ),(153476896296620391393047481115547/8084256167878642681294289062500:ℝ)],
![(7819070578557858514988442058751/71860054825587934944838125000:ℝ),(3561808114568111394338110005534653/16168512335757285362588578125000:ℝ),(463729616474599728266655214124417/3233702467151457072517715625000:ℝ),(481251063159666875602788528306407/16168512335757285362588578125000:ℝ)]]
theorem row224_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7131580474142366096971518702469/5886775691312163630681139200000000:ℝ) row224_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row224_coefficients,Fin.sum_univ_succ]
 ring
theorem row224_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row224_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row224_coefficients]
#print axioms row224_identity
#print axioms row224_pos
end
end LewkoStage2Finite
