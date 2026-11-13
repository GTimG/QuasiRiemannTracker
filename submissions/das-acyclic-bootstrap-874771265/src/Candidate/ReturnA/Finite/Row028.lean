/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12221262105141627858073821804380093/155421032364769841043750000:ℝ),(35989517509429905015646222669727159/155421032364769841043750000:ℝ),(35320667942444181767343561246694039/155421032364769841043750000:ℝ),(11552399862378681714220160381346973/155421032364769841043750000:ℝ)],
![(284882035744594146040102039469320277/1942762904559623013046875000:ℝ),(838122006162931377480554406984596639/1942762904559623013046875000:ℝ),(821734974496187538758013021833071447/1942762904559623013046875000:ℝ),(53698934267739641261869380863559017/388552580911924602609375000:ℝ)],
![(264936544899671056483326106086961229/3885525809119246026093750000:ℝ),(778619961346478483218687184219381903/3885525809119246026093750000:ℝ),(762568765967376363524149712705768269/3885525809119246026093750000:ℝ),(49777000028891846146032839414669519/777105161823849205218750000:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (49777000028891846146032839414669519/370849028398468894361124864000000000:ℝ) row028_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row028_coefficients,Fin.sum_univ_succ]
 ring
theorem row028_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row028_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row028_pos
