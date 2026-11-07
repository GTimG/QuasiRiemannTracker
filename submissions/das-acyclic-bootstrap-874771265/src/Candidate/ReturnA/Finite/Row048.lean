/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row048_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17166765331667026129580589990891894733253/498326542519851293062500000000:ℝ),(153745360130164389517332841128285516689261/1494979627559553879187500000000:ℝ),(809478349615202096648611064103429597841/7909945119362718937500000000:ℝ),(50746342672088357718128855559938361502447/1494979627559553879187500000000:ℝ)],
![(16887904085837717630085613374848883088613/249163271259925646531250000000:ℝ),(6049534432562739694885289028733520921909/29899592551191077583750000000:ℝ),(150487169856631383393571267077370460586181/747489813779776939593750000000:ℝ),(9982504002668741384102854036715817360859/149497962755955387918750000000:ℝ)],
![(16612141890501006633088345323892213922333/498326542519851293062500000000:ℝ),(148759226827031483975267910322797471936893/1494979627559553879187500000000:ℝ),(29602154161787257931904474730424340144043/298995925511910775837500000000:ℝ),(1818072901842399998063595456518550761123/55369615835539032562500000000:ℝ)]]
theorem row048_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (5454218705527199994190786369555652283369/81172715248887077337571524608000000000000:ℝ) row048_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row048_coefficients,Fin.sum_univ_succ]
 ring
theorem row048_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row048_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row048_pos
