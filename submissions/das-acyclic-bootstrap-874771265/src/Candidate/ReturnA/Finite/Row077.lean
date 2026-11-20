/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row077_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20918370190160141953132121/9333115915781250000:ℝ),(59746553254565239332254507/9333115915781250000:ℝ),(56815821766633022713584451/9333115915781250000:ℝ),(3597527740445585066892413/1866623183156250000:ℝ)],
![(19516602647736638625940937/4666557957890625000:ℝ),(55374989629705718664196619/4666557957890625000:ℝ),(52281248399581394675869327/4666557957890625000:ℝ),(3284572283522462927522729/933311591578125000:ℝ)],
![(18780613686866358469208753/9333115915781250000:ℝ),(52985808786053268344429531/9333115915781250000:ℝ),(49714225897711106803288753/9333115915781250000:ℝ),(620361231940967877122719/373324636631250000:ℝ)]]
theorem row077_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (620361231940967877122719/178157456124700262400000000:ℝ) row077_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row077_coefficients,Fin.sum_univ_succ]
 ring
theorem row077_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row077_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row077_pos
