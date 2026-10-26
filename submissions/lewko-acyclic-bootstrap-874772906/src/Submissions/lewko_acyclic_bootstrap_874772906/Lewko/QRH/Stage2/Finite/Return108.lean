/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32086036251916926140581736381/154314763313133788015625000:ℝ),(78519146091353200664624908327/154314763313133788015625000:ℝ),(12673598266558462508131794007/30862952662626757603125000:ℝ),(5617178421067722739788599363/51438254437711262671875000:ℝ)],
![(30619591086859831714066538741/77157381656566894007812500:ℝ),(13521687482371318860717324899/15431476331313378801562500:ℝ),(47079788483565215839471665773/77157381656566894007812500:ℝ),(3321974271113049518025526673/25719127218855631335937500:ℝ)],
![(55270641913525504636652938121/154314763313133788015625000:ℝ),(25882775061146547852352817987/30862952662626757603125000:ℝ),(49179158922025490031233074423/77157381656566894007812500:ℝ),(1001148143083324516397604043/6429781804713907833984375:ℝ)]]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3321974271113049518025526673/749123876184410068992000000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
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
end LewkoStage2Finite
