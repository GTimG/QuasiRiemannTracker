/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(223718049503214149649622513/1897279554375000000:ℝ),(664232836841266367776488691/1897279554375000000:ℝ),(657331063917195057911453003/1897279554375000000:ℝ),(8672651063165713591383473/75891182175000000:ℝ)],
![(209857674744784151757919201/948639777187500000:ℝ),(622696332974262983228860627/948639777187500000:ℝ),(615839906085005477341711031/948639777187500000:ℝ),(40600249571105329174153921/189727955437500000:ℝ)],
![(196417953698964275053310089/1897279554375000000:ℝ),(582428132306751398588308003/1897279554375000000:ℝ),(575623413834372448590600329/1897279554375000000:ℝ),(37922647045317065011120483/379455910875000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (37922647045317065011120483/181083414164668416000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row007_pos
