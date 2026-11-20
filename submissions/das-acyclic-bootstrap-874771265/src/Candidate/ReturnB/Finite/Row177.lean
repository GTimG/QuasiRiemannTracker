/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row177_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6514926493412230735250222649477211476893/6807703473497378056640625000000:ℝ),(7839613114012383655381026358447943410463/4084622084098426833984375000000:ℝ),(311920211693977522987396060445399280368/319111100320189596405029296875:ℝ),(4831480792850302036559446465162466944/319111100320189596405029296875:ℝ)],
![(26417194403788543883400487421502077450567/13615406946994756113281250000000:ℝ),(159715275650326123262511454726795999209697/40846220840984268339843750000000:ℝ),(644395804849460039167170010735881851176/319111100320189596405029296875:ℝ),(15760897341019450612275074969982537344/319111100320189596405029296875:ℝ)],
![(107430220472837173958475461637739301088293/108923255575958048906250000000000:ℝ),(653527630348334374820284991197138721618899/326769766727874146718750000000000:ℝ),(335371663764432136157935839264878845823/319111100320189596405029296875:ℝ),(11891886651002363823766298131559285968/319111100320189596405029296875:ℝ)]]
theorem row177_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (37745943694142984660620675509081773/19492575853024560996679680000000000000000:ℝ) row177_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row177_coefficients,Fin.sum_univ_succ]
 ring
theorem row177_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row177_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row177_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row177_pos
