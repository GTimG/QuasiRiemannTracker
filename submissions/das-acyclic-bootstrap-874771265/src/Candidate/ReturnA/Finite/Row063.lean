/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row063_coefficients : Fin 3 → Fin 4 → ℝ := ![![(110797598483598230482869352273828898347/3108420647295396820875000000000:ℝ),(326316424865692434009687548517619261441/3108420647295396820875000000000:ℝ),(320293282941445021767573712070057886241/3108420647295396820875000000000:ℝ),(104774280656092172829735515826267523147/3108420647295396820875000000000:ℝ)],
![(104104456792411163839990128759061910347/1554210323647698410437500000000:ℝ),(306316239556701064607661111260120930881/1554210323647698410437500000000:ℝ),(100124515055475283307808657080580877187/518070107882566136812500000000:ℝ),(32720525901238123824727996246894537009/518070107882566136812500000000:ℝ)],
![(97721627041811182302649513699607842387/3108420647295396820875000000000:ℝ),(287243779844762716496201817754990164049/3108420647295396820875000000000:ℝ),(56275662093807912986786284437364204663/621684129459079364175000000000:ℝ),(91855963732745374174729568131438701653/3108420647295396820875000000000:ℝ)]]
theorem row063_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (91855963732745374174729568131438701653/1483396113593875577444499456000000000000:ℝ) row063_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row063_coefficients,Fin.sum_univ_succ]
 ring
theorem row063_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row063_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row063_pos
