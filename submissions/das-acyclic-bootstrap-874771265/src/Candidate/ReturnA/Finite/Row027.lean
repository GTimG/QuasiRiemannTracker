/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![![(40472006535053881525426491202157/13332110027590365117187500:ℝ),(117885466604702253304073436874471/13332110027590365117187500:ℝ),(114403215784133947233289732517471/13332110027590365117187500:ℝ),(12329852551822155903886137281719/4444036675863455039062500:ℝ)],
![(35577508591825208979582615928541/6666055013795182558593750:ℝ),(103316801334440757039321654976327/6666055013795182558593750:ℝ),(99950796579556310823401145143531/6666055013795182558593750:ℝ),(2147419064801316283091952906383/444403667586345503906250:ℝ)],
![(49598309151007666955231324213/21331376044144584187500:ℝ),(89700492918840103645953216805783/13332110027590365117187500:ℝ),(86455093851403550760839181086741/13332110027590365117187500:ℝ),(9251101500176706197631482721361/4444036675863455039062500:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9251101500176706197631482721361/66274278420340597063680000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ]
 ring
theorem row027_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row027_pos
