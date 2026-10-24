/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![![(575741784269449718546330149021/8888073351726910078125000:ℝ),(4957155116925194469651673516613/26664220055180730234375000:ℝ),(1579239141252618405256151660279/8888073351726910078125000:ℝ),(1507743683826348549000771911287/26664220055180730234375000:ℝ)],
![(476463785150675042577382968733/4444036675863455039062500:ℝ),(4070686461906716871785797400309/13332110027590365117187500:ℝ),(3858934936989471114175505875021/13332110027590365117187500:ℝ),(1217584860766452679178107380911/13332110027590365117187500:ℝ)],
![(78531858657732559132732256969/1777614670345382015625000:ℝ),(664453191954481283041973855821/5332844011036146046875000:ℝ),(623399180651515365982636517671/5332844011036146046875000:ℝ),(21614202469794454178102436973/592538223448460671875000:ℝ)]]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21614202469794454178102436973/276142826751419154432000000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ]
 ring
theorem row039_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row039_pos
