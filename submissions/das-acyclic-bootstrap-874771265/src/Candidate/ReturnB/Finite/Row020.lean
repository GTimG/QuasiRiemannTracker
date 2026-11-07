/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row020_coefficients : Fin 3 → Fin 4 → ℝ := ![![(47538567534798902753552853394591/19932930924793443562500:ℝ),(44130159622402969781638234135982419/6229040913997951113281250:ℝ),(349557296925601668611162252256009379/49832327311983608906250000:ℝ),(38454140905608609481722338176542509/16610775770661202968750000:ℝ)],
![(2866415120937585967667081550641624/622904091399795111328125:ℝ),(14187796152797680104176717292685244/1038173485666325185546875:ℝ),(42132310524100766877493372373587229/3114520456998975556640625:ℝ),(4633665203527212869613581291246539/1038173485666325185546875:ℝ)],
![(460577104536718466551262807427598/207634697133265037109375:ℝ),(4102351646050887361794703974408782/622904091399795111328125:ℝ),(4059686380796072485383546255184682/622904091399795111328125:ℝ),(446355279030788113065222734352898/207634697133265037109375:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (223177639515394056532611367176449/1585394193248423623262208000000000:ℝ) row020_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row020_coefficients,Fin.sum_univ_succ]
 ring
theorem row020_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row020_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row020_pos
