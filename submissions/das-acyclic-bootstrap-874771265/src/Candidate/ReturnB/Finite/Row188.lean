/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row188_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1587283207522842163685822885224660847/248672082345188510250000000000000:ℝ),(372718922787117605202267327591711509/29840649881422621230000000000000:ℝ),(8761417871053238572244685901085743/1324602711355762661132812500000:ℝ),(57207134038760903298009656430497699/116565038599307114179687500000000:ℝ)],
![(2527603487707021060304627789449267039/155420051465742818906250000000000:ℝ),(15856509838574246938814145506075394541/466260154397228456718750000000000:ℝ),(243873303787058211481179488055161039/11656503859930711417968750000000:ℝ),(183077715182103222251024201886418517/58282519299653557089843750000000:ℝ)],
![(840722151027189942834374048184004033/77710025732871409453125000000000:ℝ),(5646131757930607266599949697752456247/233130077198614228359375000000000:ℝ),(1969829176259880000064974942431809447/116565038599307114179687500000000:ℝ),(405581380030045064197644288187837373/116565038599307114179687500000000:ℝ)]]
theorem row188_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (57207134038760903298009656430497699/217292981180990322769920000000000000000:ℝ) row188_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row188_coefficients,Fin.sum_univ_succ]
 ring
theorem row188_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row188_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row188_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row188_pos
