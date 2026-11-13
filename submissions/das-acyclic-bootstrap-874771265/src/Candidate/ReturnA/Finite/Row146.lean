/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row146_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22238057795486322640283812229210245991/932526194188619046262500000000000:ℝ),(51081862072784433485150744819293112593/932526194188619046262500000000000:ℝ),(18233333670825010065425471163438547711/466263097094309523131250000000000:ℝ),(126877830897408279537326603803393397/15542103236476984104375000000000:ℝ)],
![(4255264734233305093781137357766131471/93252619418861904626250000000000:ℝ),(9264723406401768887633158134653548901/93252619418861904626250000000000:ℝ),(1197450488831355994720751440667500883/18650523883772380925250000000000:ℝ),(65035240939852004372420746821255799/6216841294590793641750000000000:ℝ)],
![(218539911022111440528177505923363823/7460209553508952370100000000000:ℝ),(2485827162404982689758120316315448433/37301047767544761850500000000000:ℝ),(1742705384117221980765271263041555621/37301047767544761850500000000000:ℝ),(116358136134225785722277623660142101/12433682589181587283500000000000:ℝ)]]
theorem row146_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (65035240939852004372420746821255799/185424514199234447180562432000000000000:ℝ) row146_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row146_coefficients,Fin.sum_univ_succ]
 ring
theorem row146_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row146_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row146_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row146_pos
