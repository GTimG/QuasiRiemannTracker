/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row105_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4960392176967751967306992277/103638034104716275312500000:ℝ),(710320920236111749694611939297/8394680762482018300312500000:ℝ),(180295545268271741344837104679/4197340381241009150156250000:ℝ),(1902721427972050543212665659/381576398294637195468750000:ℝ)],
![(31630331608809090104300545319/233185576735611619453125000:ℝ),(523899065945762791664693265449/2098670190620504575078125000:ℝ),(57696839987941878715971010517/419734038124100915015625000:ℝ),(42456741660272059256366695007/2098670190620504575078125000:ℝ)],
![(50805978005454790749273723079/466371153471223238906250000:ℝ),(920726004581284517606300453837/4197340381241009150156250000:ℝ),(593059950029159923065499523941/4197340381241009150156250000:ℝ),(24103849015938676814532515563/839468076248201830031250000:ℝ)]]
theorem row105_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1902721427972050543212665659/694638634406592867840000000000:ℝ) row105_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row105_coefficients,Fin.sum_univ_succ]
 ring
theorem row105_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row105_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row105_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row105_pos
