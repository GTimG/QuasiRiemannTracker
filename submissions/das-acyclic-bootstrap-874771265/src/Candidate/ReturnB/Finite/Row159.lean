/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row159_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25136915158134378396361915233926913246773/108923255575958048906250000000000:ℝ),(151939383248113475405129136428597441667907/326769766727874146718750000000000:ℝ),(76583699227762449082169436412342471343/319111100320189596405029296875:ℝ),(1847225162726235706338366963807522256/319111100320189596405029296875:ℝ)],
![(6214356151760019078833933727259795247657/13615406946994756113281250000000:ℝ),(37215496797030533065721151342113275333423/40846220840984268339843750000000:ℝ),(146068665532579674891556483900848937816/319111100320189596405029296875:ℝ),(968597586112603193950807187008552832/319111100320189596405029296875:ℝ)],
![(1556838949566893055599042452594344615533/6807703473497378056640625000000:ℝ),(1859488317435585878391444204586437022223/4084622084098426833984375000000:ℝ),(72381036913766845787548936462902741488/319111100320189596405029296875:ℝ),(83842526219582735663109849940246144/319111100320189596405029296875:ℝ)]]
theorem row159_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (655019736090490122368045702658173/4873143963256140249169920000000000000000:ℝ) row159_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row159_coefficients,Fin.sum_univ_succ]
 ring
theorem row159_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row159_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row159_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row159_pos
