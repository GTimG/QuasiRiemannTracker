/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row149_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1528456300518855285240397578564875377/211338085986485156250000000000:ℝ),(146443982109091294468774729284375161/8453523439459406250000000000:ℝ),(5502973743519961277209829158146487391/422676171972970312500000000000:ℝ),(82512482606873808283459190070498673/28178411464864687500000000000:ℝ)],
![(1443251190387588299483079151039082443/105669042993242578125000000000:ℝ),(674814445927150904747681104631755393/21133808598648515625000000000:ℝ),(76042105599353883570862339202310131/3302157593538830566406250000:ℝ),(16750877997705268333742282745140989/3522301433108085937500000000:ℝ)],
![(1471982247483895861693518191364048247/211338085986485156250000000000:ℝ),(137098314540108728752850782492565093/8453523439459406250000000000:ℝ),(2454230799380461515099293738635814263/211338085986485156250000000000:ℝ),(33250345557442610531436157845715679/14089205732432343750000000000:ℝ)]]
theorem row149_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (33250345557442610531436157845715679/215156187901911619338240000000000000000:ℝ) row149_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row149_coefficients,Fin.sum_univ_succ]
 ring
theorem row149_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row149_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row149_coefficients]
#print axioms row149_identity
#print axioms row149_pos
end
end LewkoStage2Finite
