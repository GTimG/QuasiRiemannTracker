/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![![(311181563986099909501090657249/5925382076377978242187500:ℝ),(886507429435739345906818688747/5925382076377978242187500:ℝ),(15136053500786583234080585444071/106656877374803608359375000:ℝ),(4779913073798763446972793377107/106656877374803608359375000:ℝ)],
![(28367988729480242879270900047/329187893132109902343750:ℝ),(2160575250579344875835929061183/8888073114566967363281250:ℝ),(3042074289005159185061453139776/13332109671850451044921875:ℝ),(190006500402359745675324949981/2666421934370090208984375:ℝ)],
![(209757905155315531304682236747/5925382076377978242187500:ℝ),(70146412787474379096112422331/711045849165357389062500:ℝ),(1624652442490390826201047531177/17776146229133934726562500:ℝ),(5052523985200439990698572557/179557032617514492187500:ℝ)]]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5052523985200439990698572557/83679642237307944960000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ]
 ring
theorem row061_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row061_pos
