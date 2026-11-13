/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row083_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11470190027982100864103790489848793221/9192647785859054417988281250:ℝ),(33750740867821099294889344458518285327/9192647785859054417988281250:ℝ),(33096413592600767123058692634817732591/9192647785859054417988281250:ℝ),(2163170504471779062776334408229648097/1838529557171810883597656250:ℝ)],
![(2247360695918139264816270653871136033/919264778585905441798828125:ℝ),(4720545994821396891960896339076451193/656617698989932458427734375:ℝ),(32382802381789967127229271165484248407/4596323892929527208994140625:ℝ),(1510824790373921100827570816793538603/656617698989932458427734375:ℝ)],
![(11032806095085386589402421718882729309/9192647785859054417988281250:ℝ),(30162625008138932115777223996784837/8551300265915399458593750:ℝ),(31756862136809461620647972061970427773/9192647785859054417988281250:ℝ),(10364835846750302927196005820246957307/9192647785859054417988281250:ℝ)]]
theorem row083_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (10364835846750302927196005820246957307/4492188058045036087835759738880000000000:ℝ) row083_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row083_coefficients,Fin.sum_univ_succ]
 ring
theorem row083_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row083_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row083_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row083_pos
