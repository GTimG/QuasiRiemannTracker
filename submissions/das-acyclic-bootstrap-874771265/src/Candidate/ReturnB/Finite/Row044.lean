/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14764791621659562738729047826599/9486397645312500000000:ℝ),(1762292245733901373726942701407/379455905812500000000:ℝ),(29213836247367131799914772891139/6324265096875000000000:ℝ),(645699548860565604241228427917/421617673125000000000:ℝ)],
![(4772651853614058067747417117247/1581066274218750000000:ℝ),(949262421452691443929810125599/105404418281250000000:ℝ),(442502900628697773760816902599/49408321069335937500:ℝ),(156460278398067172304880203881/52702209140625000000:ℝ)],
![(13880673329702138498720953194289/9486397645312500000000:ℝ),(1656199116559581967719469107091/379455905812500000000:ℝ),(508252759147558379708732748001/117116020312500000000:ℝ),(27563977589221854670993087081/19164439687500000000:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (27563977589221854670993087081/292660059391918080000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row044_pos
