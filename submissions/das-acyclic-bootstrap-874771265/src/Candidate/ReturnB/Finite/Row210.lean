/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row210_coefficients : Fin 3 → Fin 4 → ℝ := ![![(59867022864862923976715589624586082308/2417012448450378685524052734375:ℝ),(15929737147927843826634022722750003764/268556938716708742836005859375:ℝ),(3995009241205614090893422214862705664/89518979572236247612001953125:ℝ),(4872361780755479787940516285382070272/483402489690075737104810546875:ℝ)],
![(4784795726282408399133422356253973764/96680497938015147420962109375:ℝ),(95108950755978770781805884737302639676/805670816150126228508017578125:ℝ),(213274181357064730596003489723155065856/2417012448450378685524052734375:ℝ),(47561491419505695586282751442127740928/2417012448450378685524052734375:ℝ)],
![(60682796363954048096618863763892389617/2417012448450378685524052734375:ℝ),(48244129466818362890508037369842671159/805670816150126228508017578125:ℝ),(108165605902811343180303144767713680128/2417012448450378685524052734375:ℝ),(8037703905633451982208587706799456256/805670816150126228508017578125:ℝ)]]
theorem row210_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (5805846120545128855747406181900359/36045102153191883101184983040000000000:ℝ) row210_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row210_coefficients,Fin.sum_univ_succ]
 ring
theorem row210_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row210_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row210_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row210_pos
