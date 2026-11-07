/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row158_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1286321738040851422001374499681354720833/5446162778797902445312500000000:ℝ),(39590023476284505969334116420148046751667/81692441681968536679687500000000:ℝ),(16786685760979462575420165727954767412/63822220064037919281005859375:ℝ),(4653856686645992687777334774219591448/319111100320189596405029296875:ℝ)],
![(2511545507259821170372618501138129704647/5446162778797902445312500000000:ℝ),(15230822357843059958441647256184164589409/16338488336393707335937500000000:ℝ),(30995196693790032505019098081383823844/63822220064037919281005859375:ℝ),(931384085657137332145480710870852016/63822220064037919281005859375:ℝ)],
![(993438580860156384908000187459742591613/4356930223038321956250000000000:ℝ),(1193846620147514051537375532013578444479/2614158133822993173750000000000:ℝ),(2957545010920098785046262029661662287/12764444012807583856201171875:ℝ),(38621353778916368840029536274955368/12764444012807583856201171875:ℝ)]]
theorem row158_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4827669222364546105003692034369421/3118812136483929759468748800000000000000:ℝ) row158_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row158_coefficients,Fin.sum_univ_succ]
 ring
theorem row158_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row158_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row158_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row158_pos
