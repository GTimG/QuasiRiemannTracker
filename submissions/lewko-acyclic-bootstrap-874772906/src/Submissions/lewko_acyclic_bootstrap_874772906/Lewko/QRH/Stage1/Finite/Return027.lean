/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8094726740514027051627316128173/2666445342107652210937500:ℝ),(23578048567725647795400533092519/2666445342107652210937500:ℝ),(22881577364347021618704977375519/2666445342107652210937500:ℝ),(2466071975571145701186628470391/888815114035884070312500:ℝ)],
![(7115809752537537909105125905949/1333222671053826105468750:ℝ),(1087592809195489200757713077437/70169614265990847656250:ℝ),(19991041444135608322352673250859/1333222671053826105468750:ℝ),(429502950032979417903479212367/88881511403588407031250:ℝ)],
![(1240015910255701635928829064481/533289068421530442187500:ℝ),(17940950359506784414041455434327/2666445342107652210937500:ℝ),(17291849615251488923904483673109/2666445342107652210937500:ℝ),(1850310292804212175382401603729/888815114035884070312500:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1850310292804212175382401603729/13254971690884141154304000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ]
 ring
theorem row027_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
#print axioms row027_identity
#print axioms row027_pos
end
end LewkoStage1Finite
