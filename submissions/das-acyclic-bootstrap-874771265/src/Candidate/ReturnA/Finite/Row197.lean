/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28203575950570181932835626672/15337262529441826171875:ℝ),(206328034512739603803944052752/46011787588325478515625:ℝ),(160348900932120289216206624256/46011787588325478515625:ℝ),(7726318854218246242153890304/9202357517665095703125:ℝ)],
![(17454061923961739558303427368/5112420843147275390625:ℝ),(372992005705412374564669220968/46011787588325478515625:ℝ),(11113535805172818020440659968/1840471503533019140625:ℝ),(61932946739563731971078124544/46011787588325478515625:ℝ)],
![(25193032923323416569020914307/15337262529441826171875:ℝ),(175897995220656954354541221641/46011787588325478515625:ℝ),(126648336090685122087094697344/46011787588325478515625:ℝ),(26329439639998417439616218624/46011787588325478515625:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (51424686796871909061750427/171544377536767918080000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ]
 ring
theorem row197_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row197_pos
