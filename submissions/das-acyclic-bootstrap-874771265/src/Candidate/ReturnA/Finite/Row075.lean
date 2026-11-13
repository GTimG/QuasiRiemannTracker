/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row075_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2808684783305333109703/194439914912109375:ℝ),(22677794196031116466739/583319744736328125:ℝ),(472829301556906677607/13565575458984375:ℝ),(6079920120831869999471/583319744736328125:ℝ)],
![(1928287334060401966979/77775965964843750:ℝ),(75212222817195173461541/1166639489472656250:ℝ),(32381225569579639164026/583319744736328125:ℝ),(9237269166435067185598/583319744736328125:ℝ)],
![(71629416836238648018149/6222077277187500000:ℝ),(540974889147389702131183/18666231831562500000:ℝ),(111746341036442866727/4666557957890625:ℝ),(3778085172096803400977/583319744736328125:ℝ)]]
theorem row075_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3778085172096803400977/1087386817167360000000000:ℝ) row075_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row075_coefficients,Fin.sum_univ_succ]
 ring
theorem row075_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row075_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row075_pos
