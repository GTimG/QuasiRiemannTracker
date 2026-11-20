/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![![(247398971592897834994162242288809/53328438687401804179687500:ℝ),(79776075579931721368506114503497/5925382076377978242187500:ℝ),(19282813343018162829180017790854/1481345519094494560546875:ℝ),(1016332488885992686043502311264/242401994033644564453125:ℝ)],
![(23267328657820321150386387010619/2666421934370090208984375:ℝ),(112340792675320708399440588213269/4444036557283483681640625:ℝ),(325244033840112766856877526555304/13332109671850451044921875:ℝ),(11617447700151170613950004524288/1481345519094494560546875:ℝ)],
![(4969576665833342368638831598459/1212009970168222822265625:ℝ),(957934091624037459227750640413/80800664677881521484375:ℝ),(13839019599194747037979111340488/1212009970168222822265625:ℝ),(4439524423910779333204652082752/1212009970168222822265625:ℝ)]]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (69367569123605927081322688793/1129675170203657256960000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ]
 ring
theorem row068_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row068_pos
