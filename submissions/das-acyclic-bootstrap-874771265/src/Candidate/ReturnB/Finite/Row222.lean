/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row222_coefficients : Fin 3 → Fin 4 → ℝ := ![![(37980460249819738304647763450081293/418033776661900373004960937500:ℝ),(172649307039823560825707934957129587/919674308656180820610914062500:ℝ),(41566784001962412447169412266752848/383197628606742008587880859375:ℝ),(13266626904927134931163064427507616/1149592885820226025763642578125:ℝ)],
![(242506317146171517070134591285047137/1149592885820226025763642578125:ℝ),(521232340361740998290140714733031473/1149592885820226025763642578125:ℝ),(17908796162975118248988623618730496/62705066499285055950744140625:ℝ),(148376046819760632105265851654974272/3448778657460678077290927734375:ℝ)],
![(531612892866817227911192270670997/4180337766619003730049609375:ℝ),(329317578098718344206821184260320383/1149592885820226025763642578125:ℝ),(681097503920754858020646374352079648/3448778657460678077290927734375:ℝ),(131500339693591338083107356905941024/3448778657460678077290927734375:ℝ)]]
theorem row222_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (414582090778972966598845763359613/2142996461941029911450910720000000000:ℝ) row222_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row222_coefficients,Fin.sum_univ_succ]
 ring
theorem row222_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row222_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row222_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row222_pos
