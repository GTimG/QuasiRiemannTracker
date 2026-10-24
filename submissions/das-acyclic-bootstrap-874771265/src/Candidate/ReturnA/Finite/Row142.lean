/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row142_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6281245289320187186103824037212959/596816764280716189608000000000000:ℝ),(314232988806989086794893208079637437/14920419107017904740200000000000000:ℝ),(193731216645920374527280695938250287/14920419107017904740200000000000000:ℝ),(1380635455658376858406426693557473/596816764280716189608000000000000:ℝ)],
![(2283222116600499331039208592370643/59681676428071618960800000000000:ℝ),(556060153369236576059313846814303189/7460209553508952370100000000000000:ℝ),(325596693002722709759194735812286709/7460209553508952370100000000000000:ℝ),(10182471369519091646027424028862779/1492041910701790474020000000000000:ℝ)],
![(35649112333667724191744261886493471/596816764280716189608000000000000:ℝ),(2035621525928490694327872675530492533/14920419107017904740200000000000000:ℝ),(1530863803865824341814882436584871213/14920419107017904740200000000000000:ℝ),(75683238311424113716265324483343091/2984083821403580948040000000000000:ℝ)]]
theorem row142_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1380635455658376858406426693557473/271617940721534834737152000000000000:ℝ) row142_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row142_coefficients,Fin.sum_univ_succ]
 ring
theorem row142_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row142_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row142_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row142_pos
