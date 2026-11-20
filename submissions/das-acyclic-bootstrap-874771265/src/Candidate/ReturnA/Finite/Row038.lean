/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![![(72577683312302345887751342597/26664220055180730234375000:ℝ),(4497704381089817220497846479/592538223448460671875000:ℝ),(187728732263736744670562066419/26664220055180730234375000:ℝ),(19299574824443992482386772487/8888073351726910078125000:ℝ)],
![(5916955124772522790076367673/1481345558621151679687500:ℝ),(144957696182007150830777802121/13332110027590365117187500:ℝ),(131005690628114178706198214221/13332110027590365117187500:ℝ),(13094699879520575234327573719/4444036675863455039062500:ℝ)],
![(40040532039487687952170353067/26664220055180730234375000:ℝ),(52768726690843158826850790331/13332110027590365117187500:ℝ),(45996848881511512740366706799/13332110027590365117187500:ℝ),(8824013341692461618171562001/8888073351726910078125000:ℝ)]]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8824013341692461618171562001/129441950039727728640000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ]
 ring
theorem row038_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row038_pos
