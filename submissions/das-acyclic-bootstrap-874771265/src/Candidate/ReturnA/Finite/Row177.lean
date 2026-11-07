/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row177_coefficients : Fin 3 → Fin 4 → ℝ := ![![(325772123269639156576482581458521528482917/340389546071069248141992187500000:ℝ),(392024020934202417751798271573337107894683/204233727642641548885195312500000:ℝ),(31198321020498691838307359581886476704992/31911519944162742013311767578125:ℝ),(97018145496414048305761668656720530688/6382303988832548402662353515625:ℝ)],
![(1320963321573518117752411995964550449063711/680779092142138496283984375000000:ℝ),(1597326903967340127572300417463578253280993/408467455285283097770390625000000:ℝ),(64452230246750661134938887232029488494288/31911519944162742013311767578125:ℝ),(63199621299993441211690614738322217216/1276460797766509680532470703125:ℝ)],
![(5371927313319775714406834794566858069956653/5446232737137107970271875000000000:ℝ),(6535976099476634690549204474265832187903443/3267739642282264782163125000000000:ℝ),(4791931538366979130144757833500283355234/4558788563451820287615966796875:ℝ),(47645932218835815898567960910427904288/1276460797766509680532470703125:ℝ)]]
theorem row177_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (378977130845367376194381518190314573/194928262436737028336155361280000000000000:ℝ) row177_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row177_coefficients,Fin.sum_univ_succ]
 ring
theorem row177_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row177_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row177_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row177_pos
