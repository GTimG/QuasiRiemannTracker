/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row066_coefficients : Fin 3 → Fin 4 → ℝ := ![![(159493186702346237105596755881559551197/155420051465742818906250000000:ℝ),(94753577542797812985282933769842836777/31084010293148563781250000000:ℝ),(312718511221698167349633672931684751737/103613367643828545937500000000:ℝ),(6880134615965560729066822313549888663/6907557842921903062500000000:ℝ)],
![(154325901671487008895156931454091945239/77710025732871409453125000000:ℝ),(91659607393084528702754513683788894733/15542005146574281890625000000:ℝ),(25202230852347151897738281151349472007/4317223651826189414062500000:ℝ),(166297757983477132671631122232708853/86344473036523788281250000:ℝ)],
![(49760483751440500999292524918345033001/51806683821914272968750000000:ℝ),(656586730119871449577726380021018211/230251928097396768750000000:ℝ),(146189917292521904778474412384905260329/51806683821914272968750000000:ℝ),(3214558255873289418905760619901413057/3453778921460951531250000000:ℝ)]]
theorem row066_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (3214558255873289418905760619901413057/52742640054360673307590656000000000000:ℝ) row066_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row066_coefficients,Fin.sum_univ_succ]
 ring
theorem row066_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row066_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row066_pos
