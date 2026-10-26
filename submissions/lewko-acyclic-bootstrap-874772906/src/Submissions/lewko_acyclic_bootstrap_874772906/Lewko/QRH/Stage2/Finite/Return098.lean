/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row098_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1713547554006370509895650641700842726/1123018320036839972873719921875:ℝ),(680040650552026286290130332540333694/160431188576691424696245703125:ℝ),(337833234985052637019036770492412426/86386024618218459451824609375:ℝ),(1345011708717717917314966330319868406/1123018320036839972873719921875:ℝ)],
![(343434011154114407599421323552546652/114593706126208160497318359375:ℝ),(3578010304308088978124126851573410692/431930123091092297259123046875:ℝ),(42668028190397223470493278555295834268/5615091600184199864368599609375:ℝ),(2596257129105413518876029867783256244/1123018320036839972873719921875:ℝ)],
![(8559460006729219307074667692139248738/5615091600184199864368599609375:ℝ),(4719933064881307869322467219360554522/1123018320036839972873719921875:ℝ),(21586108872425176862865393203889949607/5615091600184199864368599609375:ℝ),(187012688818689689387725262120755021/160431188576691424696245703125:ℝ)]]
theorem row098_identity (δ p : ℝ) : rowMargin .oldSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (649064282276353379719007466945814061/267962608742616066593230789017600000000:ℝ) row098_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row098_coefficients,Fin.sum_univ_succ]
 ring
theorem row098_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .P δ p := by
 rw [row098_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row098_coefficients]
#print axioms row098_identity
#print axioms row098_pos
end
end LewkoStage2Finite
