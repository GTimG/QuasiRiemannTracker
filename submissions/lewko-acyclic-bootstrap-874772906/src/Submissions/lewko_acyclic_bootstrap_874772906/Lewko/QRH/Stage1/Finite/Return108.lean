/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4363697080755739958217968027/20986808068732307653125000:ℝ),(53392967267569908983836403621/104934040343661538265625000:ℝ),(43090187323906634264527313257/104934040343661538265625000:ℝ),(3819676676629289980843583257/34978013447887179421875000:ℝ)],
![(832852556889699010188243559/2098680806873230765312500:ℝ),(9194743620107134293907059337/10493404034366153826562500:ℝ),(1280569644480851034263162047/2098680806873230765312500:ℝ),(451788252559116463191656231/3497801344788717942187500:ℝ)],
![(7516807712022079212351234383/20986808068732307653125000:ℝ),(88001444472752249076445992509/104934040343661538265625000:ℝ),(1760096527578258572492752211/2761422114306882585937500:ℝ),(680780934054998904134260976/4372251680985897427734375:ℝ)]]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (451788252559116463191656231/101880848414254852915200000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row108_coefficients,Fin.sum_univ_succ]
 ring
theorem row108_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row108_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row108_coefficients]
#print axioms row108_identity
#print axioms row108_pos
end
end LewkoStage1Finite
