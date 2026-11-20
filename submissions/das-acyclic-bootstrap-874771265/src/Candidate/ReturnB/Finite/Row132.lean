/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row132_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71712630802830602618260381618363/1049335095310252287539062500:ℝ),(189005262771933385597040583609089/1049335095310252287539062500:ℝ),(164290379016100071925681870050589/1049335095310252287539062500:ℝ),(15661192503990098847857847686621/349778365103417429179687500:ℝ)],
![(1320070577365470969583871183461/9539409957365929886718750:ℝ),(189264650018189537328721298143217/524667547655126143769531250:ℝ),(14750886468188088327735541122329/47697049786829649433593750:ℝ),(15194465466150215319940543930919/174889182551708714589843750:ℝ)],
![(81629165517467229943210518641047/1049335095310252287539062500:ℝ),(42691317085454442587518106602789/209867019062050457507812500:ℝ),(45925703455062272474949774332356/262333773827563071884765625:ℝ),(8643041462176907682898675284421/174889182551708714589843750:ℝ)]]
theorem row132_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (15194465466150215319940543930919/5216273051970574708899840000000000:ℝ) row132_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row132_coefficients,Fin.sum_univ_succ]
 ring
theorem row132_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row132_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row132_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row132_pos
