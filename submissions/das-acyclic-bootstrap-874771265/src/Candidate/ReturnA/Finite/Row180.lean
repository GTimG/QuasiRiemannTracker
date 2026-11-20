/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row180_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60726787268377509318614428751369387/29840838214035809480400000000000:ℝ),(662174103394704791622770827788172477/149204191070179047402000000000000:ℝ),(439531365343568457495788650023862199/149204191070179047402000000000000:ℝ),(80487829870632075984884360630036657/149204191070179047402000000000000:ℝ)],
![(2073023458768559764036233197718104699/373010477675447618505000000000000:ℝ),(939896161087983282194279973937262797/74602095535089523701000000000000:ℝ),(3333974966875102075602647179872883597/373010477675447618505000000000000:ℝ),(704497409683030609780246875729674311/373010477675447618505000000000000:ℝ)],
![(17089452852840925476745136298194472151/3730104776754476185050000000000000:ℝ),(41821309029591436905079466498964728677/3730104776754476185050000000000000:ℝ),(33284205455397905424085405181350787789/3730104776754476185050000000000000:ℝ),(8534228015523105082427673187530531263/3730104776754476185050000000000000:ℝ)]]
theorem row180_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (80487829870632075984884360630036657/69534192824712917692710912000000000000:ℝ) row180_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row180_coefficients,Fin.sum_univ_succ]
 ring
theorem row180_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row180_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row180_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row180_pos
