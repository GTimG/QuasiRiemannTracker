/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16811337028820846992762802711981/106656877374803608359375000:ℝ),(47357565629998983191892142812217/106656877374803608359375000:ℝ),(11097527726054567387022966224179/26664219343700902089843750:ℝ),(346063800859791831975695932412/2666421934370090208984375:ℝ)],
![(341650527323435111369658214403/1212009970168222822265625:ℝ),(10518355379076252228444848849933/13332109671850451044921875:ℝ),(9790732139199161545927274384492/13332109671850451044921875:ℝ),(3030169760140206432566478392992/13332109671850451044921875:ℝ)],
![(559781736689786574258411151342/4444036557283483681640625:ℝ),(1555292391183499573811661972278/4444036557283483681640625:ℝ),(95746308707216528472418802392/296269103818898912109375:ℝ),(440618012379900543899906214944/4444036557283483681640625:ℝ)]]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13769312886871891996872069217/258883893171671454720000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ]
 ring
theorem row069_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row069_pos
