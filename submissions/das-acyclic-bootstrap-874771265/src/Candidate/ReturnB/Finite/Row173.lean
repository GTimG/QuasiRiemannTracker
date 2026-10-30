/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row173_coefficients : Fin 3 → Fin 4 → ℝ := ![![(406403939454044648975144839329715596813823033/27230813893989512226562500000000:ℝ),(24378225993367552163669687086519782422560963/816924416819685366796875000000:ℝ),(4760989695350461401745723036811454042482432/319111100320189596405029296875:ℝ),(790947208865552138324492945991286030336/319111100320189596405029296875:ℝ)],
![(50839034052752865688890701389716661001900231/1701925868374344514160156250000:ℝ),(76250572106378428164165788202299923284304373/1276444401280758385620117187500:ℝ),(9534610088117782808000411844926422910930944/319111100320189596405029296875:ℝ),(857035237555316974188323882258314756096/63822220064037919281005859375:ℝ)],
![(6364956285944166827691060111489029360120377/425481467093586128540039062500:ℝ),(9551729765098718958144419775174350274291979/319111100320189596405029296875:ℝ),(4785449442427851148626641965792450078195712/319111100320189596405029296875:ℝ),(7436506520115882388632669256424114716672/319111100320189596405029296875:ℝ)]]
theorem row173_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (24137793239305180002578520080300477/19960397673497150460599992320000000000000000:ℝ) row173_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row173_coefficients,Fin.sum_univ_succ]
 ring
theorem row173_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row173_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row173_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row173_pos
