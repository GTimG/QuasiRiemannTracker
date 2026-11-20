/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![![(38682035575813100907962214559763/524667547655126143769531250:ℝ),(105159382385984065067619903988387/524667547655126143769531250:ℝ),(37945010722818803061306980249729/209867019062050457507812500:ℝ),(18919627556793407713507913713799/349778365103417429179687500:ℝ)],
![(35060644646900238308765946256409/262333773827563071884765625:ℝ),(93322801927698878994866001087151/262333773827563071884765625:ℝ),(3284414704237033927412898417098/10493350953102522875390625:ℝ),(7947278011455020305908249782236/87444591275854357294921875:ℝ)],
![(7101254024607077732638442598481/104933509531025228753906250:ℝ),(18690499110165390972141271670843/104933509531025228753906250:ℝ),(16219010734582059605005400314993/104933509531025228753906250:ℝ),(1542782898507015708389919580877/34977836510341742917968750:ℝ)]]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1542782898507015708389919580877/521627305197057470889984000000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ]
 ring
theorem row076_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row076_pos
