/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row202_coefficients : Fin 3 → Fin 4 → ℝ := ![![(431655277001202912565794730481936161949/2417012448450378685524052734375:ℝ),(128699337704709453366482305268721005407/268556938716708742836005859375:ℝ),(1023013007722700016921512775873123244279/2417012448450378685524052734375:ℝ),(731781628304684096165054943542457673/5967931971482416507466796875:ℝ)],
![(166527939824972866858171974958631533874/483402489690075737104810546875:ℝ),(740192467789162828648868499317538489146/805670816150126228508017578125:ℝ),(216228050387090230265737520662693825774/268556938716708742836005859375:ℝ),(558109306722890529982123588495724133898/2417012448450378685524052734375:ℝ)],
![(408423830697715518485056300168254530021/2417012448450378685524052734375:ℝ),(14460468783222160451353361785722086213/32226832646005049140320703125:ℝ),(945225032163726497180213036285079802337/2417012448450378685524052734375:ℝ),(269110947054589856234555541196560678883/2417012448450378685524052734375:ℝ)]]
theorem row202_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (269110947054589856234555541196560678883/1181125907355791625459629524254720000000000:ℝ) row202_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row202_coefficients,Fin.sum_univ_succ]
 ring
theorem row202_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row202_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row202_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row202_pos
