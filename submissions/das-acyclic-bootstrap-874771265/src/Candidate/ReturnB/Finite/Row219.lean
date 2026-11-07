/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row219_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3120157919762570226313527460793235776/483402489690075737104810546875:ℝ),(2479628209389607479903653526071158976/161134163230025245701603515625:ℝ),(5555675978787280817128993323553046528/483402489690075737104810546875:ℝ),(1236800466053006983669537668632805376/483402489690075737104810546875:ℝ)],
![(33004355054806407465585253400779203152/2417012448450378685524052734375:ℝ),(8803442112449391962415283687564327952/268556938716708742836005859375:ℝ),(3989463271363331939467559199167885312/161134163230025245701603515625:ℝ),(13613799868849637290225357190843531264/2417012448450378685524052734375:ℝ)],
![(18333491527750318429016510578942152097/2417012448450378685524052734375:ℝ),(14936575445023262076331804233127231751/805670816150126228508017578125:ℝ),(6964048646962353608958095243120942848/483402489690075737104810546875:ℝ),(2781075579918887223974420650953494528/805670816150126228508017578125:ℝ)]]
theorem row219_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (9436038711952262753826428746283/56320472114362317345601536000000000:ℝ) row219_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row219_coefficients,Fin.sum_univ_succ]
 ring
theorem row219_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row219_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row219_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row219_pos
