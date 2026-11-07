/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row162_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5623541477684438900346879194338502100895927/4084674552852830977703906250000000:ℝ),(1871325377214078518121674570349564123110099/583524936121832996814843750000000:ℝ),(9347552596609794596993317132078545162322141/4084674552852830977703906250000000:ℝ),(1663819816188007858065579102956612745731/3630821824758071980181250000000:ℝ)],
![(5639142863073689466369537673662486924396799/2042337276426415488851953125000000:ℝ),(1873933699148029500220149746547032204905763/291762468060916498407421875000000:ℝ),(9337386346607478381934926343944457853622487/2042337276426415488851953125000000:ℝ),(41310534496994086945760014550388959373421/45385272809475899752265625000000:ℝ)],
![(5754192526738083698059756934107265346939493/4084674552852830977703906250000000:ℝ),(13433692578412340644729583029545691845324857/4084674552852830977703906250000000:ℝ),(19249345747140808294813616998999723877151773/8169349105705661955407812500000000:ℝ),(9605695975967181264479502327413105086589/20171232359767066556562500000000:ℝ)]]
theorem row162_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (41310534496994086945760014550388959373421/1419424289672666432115364195205120000000000000:ℝ) row162_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row162_coefficients,Fin.sum_univ_succ]
 ring
theorem row162_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row162_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row162_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row162_pos
