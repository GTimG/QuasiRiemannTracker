/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(182045588577246887820686669/52702209140625000:ℝ),(325859508349530986789927707/31621325484375000:ℝ),(3240396598537629162280525513/316213254843750000:ℝ),(358025015501933540435122819/105404418281250000:ℝ)],
![(528001405276133493007575677/79053313710937500:ℝ),(1574924302390468673487076531/79053313710937500:ℝ),(391464536795883151620905384/19763328427734375:ℝ),(86489208344866237667353447/13175552285156250:ℝ)],
![(510150722217944444609546737/158106627421875000:ℝ),(507135740931033236688092809/52702209140625000:ℝ),(1512376285812365105083632113/158106627421875000:ℝ),(15185448037491207261481831/4791109921875000:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (15185448037491207261481831/73165014847979520000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ]
 ring
theorem row009_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row009_pos
