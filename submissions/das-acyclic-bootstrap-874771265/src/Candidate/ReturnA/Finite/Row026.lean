/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![![(789463835239356556535358581843/6666055013795182558593750:ℝ),(2251949679835162638552704925779/6666055013795182558593750:ℝ),(4277202024655227672414741008933/13332110027590365117187500:ℝ),(1352180820708838572633954571061/13332110027590365117187500:ℝ)],
![(629516129307322957514025434561/3333027506897591279296875:ℝ),(1778914116011826726042779953727/3333027506897591279296875:ℝ),(1672565045185893199235766952396/3333027506897591279296875:ℝ),(104627469925704653851871236646/666605501379518255859375:ℝ)],
![(488695426418692992695674073429/6666055013795182558593750:ℝ),(54557049739832850269536616639/266642200551807302343750:ℝ),(1265196542277148373311716234613/6666055013795182558593750:ℝ),(389930074576580715531787392067/6666055013795182558593750:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (389930074576580715531787392067/3106606800953465487360000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ]
 ring
theorem row026_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row026_pos
