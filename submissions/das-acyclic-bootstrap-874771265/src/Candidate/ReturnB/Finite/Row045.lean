/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row045_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29291908817603680894241140712663/18972795290625000000000:ℝ),(29134552268962001285181647077789/6324265096875000000000:ℝ),(169790275507089061499591398088/37056240802001953125:ℝ),(18763589238507341488598304232/12352080267333984375:ℝ)],
![(14199139615265159859132149077489/4743198822656250000000:ℝ),(427893086393117472915915955867/47911099218750000000:ℝ),(36567655791823835934928105408/4117360089111328125:ℝ),(109091121363496789355419116224/37056240802001953125:ℝ)],
![(6880941733051966206917254416647/4743198822656250000000:ℝ),(621964903444757919265468306471/143733297656250000000:ℝ),(159430681673733570188027526448/37056240802001953125:ℝ),(52837712293850405118940028816/37056240802001953125:ℝ)]]
theorem row045_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (3302357018365650319933751801/35367853857177600000000000000:ℝ) row045_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row045_coefficients,Fin.sum_univ_succ]
 ring
theorem row045_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row045_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row045_pos
