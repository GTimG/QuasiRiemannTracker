/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row150_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5317912980438155080238343342576629/1036772591751562500000000000:ℝ),(11564260469884307862806893945679861/1036772591751562500000000000:ℝ),(7076835670553728189909800548827/1012473234132385253906250:ℝ),(488443475195734806591350175242/506236617066192626953125:ℝ)],
![(2373612251361751843422091020604387/259193147937890625000000000:ℝ),(4850523848875240890281040665376739/259193147937890625000000000:ℝ),(5111123432312564677262005985794/506236617066192626953125:ℝ),(273405468419031382615619960848/506236617066192626953125:ℝ)],
![(1182165768943250183983302990708101/259193147937890625000000000:ℝ),(2371855957211909565258814718945669/259193147937890625000000000:ℝ),(2374865576194783605373009414946/506236617066192626953125:ℝ),(51251927232558251319275570732/506236617066192626953125:ℝ)]]
theorem row150_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (12812981808139562829818892683/1932684190521753600000000000000000:ℝ) row150_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row150_coefficients,Fin.sum_univ_succ]
 ring
theorem row150_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row150_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row150_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row150_pos
