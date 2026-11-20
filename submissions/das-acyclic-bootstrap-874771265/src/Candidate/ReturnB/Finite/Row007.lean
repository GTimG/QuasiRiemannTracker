/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(149145355668061648831849369/1264853019375000000:ℝ),(442821859392701874484392683/1264853019375000000:ℝ),(438220677612141681636833539/1264853019375000000:ℝ),(642418550611117582152401/5621568975000000:ℝ)],
![(139905106050546261662965513/632426509687500000:ℝ),(415130857480088874774075851/632426509687500000:ℝ),(410559906390531422839930703/632426509687500000:ℝ),(27066830992197761945764073/126485301937500000:ℝ)],
![(130945292242260116195702257/1264853019375000000:ℝ),(388285391036415499137494939/1264853019375000000:ℝ),(127916304075349889490532859/421617673125000000:ℝ),(25281762686378857105961179/252970603875000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (25281762686378857105961179/120722274499166208000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row007_pos
