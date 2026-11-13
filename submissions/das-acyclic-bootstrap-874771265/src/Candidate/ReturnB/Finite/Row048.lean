/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row048_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20599933716972508287435202979224179687037/597987927743803306875000000000:ℝ),(20499197189125659818626282493952216825341/199329309247934435625000000000:ℝ),(61196012302883117660855485031349268949207/597987927743803306875000000000:ℝ),(6766117981489979387159562429572266053407/199329309247934435625000000000:ℝ)],
![(20265303083032400664161751209935422674077/298993963871901653437500000000:ℝ),(268865779663002561176177692305868542487/1328862061652896237500000000:ℝ),(20064775199305979052196533423356024411861/99664654623967217812500000000:ℝ),(3992965548416345623112135196236614770017/59798792774380330687500000000:ℝ)],
![(1812217388942537611136859405925197902687/54362538885800300625000000000:ℝ),(1803125918746818114783173111109128044103/18120846295266766875000000000:ℝ),(34723621388957372170786213209589478029/350726057327743875000000000:ℝ),(1785000900584538662682165447584182864873/54362538885800300625000000000:ℝ)]]
theorem row048_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1785000900584538662682165447584182864873/26565441609049949294517288960000000000000:ℝ) row048_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row048_coefficients,Fin.sum_univ_succ]
 ring
theorem row048_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row048_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row048_pos
