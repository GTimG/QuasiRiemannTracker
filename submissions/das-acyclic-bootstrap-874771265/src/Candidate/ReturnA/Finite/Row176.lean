/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row176_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2956646897110071643444205462196378199272841/8169349105705661955407812500000000:ℝ),(6885944183769365175084908383149332342486179/8169349105705661955407812500000000:ℝ),(4922175828776511793233812584601936044822169/8169349105705661955407812500000000:ℝ),(992839273088343717458369611360639870358831/8169349105705661955407812500000000:ℝ)],
![(605022777150534661300018983803749578256457/816934910570566195540781250000000:ℝ),(7076379250145579493188848640809870218589963/4084674552852830977703906250000000:ℝ),(2548884320266583178222472995549572484343819/2042337276426415488851953125000000:ℝ),(1868685283166478913924668967414344420991/7294061701522912460185546875000:ℝ)],
![(3118666897644282503631451107786420734168767/8169349105705661955407812500000000:ℝ),(1468369535865764745916294280744537353326899/1633869821141132391081562500000000:ℝ),(2139268345195862213263394747980417828475909/3267739642282264782163125000000000:ℝ),(2249900627253797165108299654847248561823089/16338698211411323910815625000000000:ℝ)]]
theorem row176_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (992839273088343717458369611360639870358831/15968523258817497361297847196057600000000000000:ℝ) row176_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row176_coefficients,Fin.sum_univ_succ]
 ring
theorem row176_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row176_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row176_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row176_pos
