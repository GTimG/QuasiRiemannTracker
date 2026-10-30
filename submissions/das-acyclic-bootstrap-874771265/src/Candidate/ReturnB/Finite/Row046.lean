/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![![(548339490071157133056044248577486/13332109671850451044921875:ℝ),(539939708566459338758027685963104/4444036557283483681640625:ℝ),(3189610016079279161977170536652557/26664219343700902089843750:ℝ),(69776650174555262445818533076927/1777614622913393472656250:ℝ)],
![(1032066066218267962498550269155496/13332109671850451044921875:ℝ),(112826383623265082771618599729496/493781839698164853515625:ℝ),(332978508953082603960892425638644/1481345519094494560546875:ℝ),(39302369781682231422880883788276/533284386874018041796875:ℝ)],
![(97030823922685556371118441079052/2666421934370090208984375:ℝ),(95384414394377090786188787111852/888807311456696736328125:ℝ),(281252980480325823125974062458956/2666421934370090208984375:ℝ),(92130451280322383165804267202452/2666421934370090208984375:ℝ)]]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (23032612820080595791451066800613/318116527929349883559936000000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ]
 ring
theorem row046_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row046_pos
