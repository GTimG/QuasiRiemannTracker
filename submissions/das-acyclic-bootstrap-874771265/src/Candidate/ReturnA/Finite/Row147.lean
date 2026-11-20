/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row147_coefficients : Fin 3 → Fin 4 → ℝ := ![![(959781501013414922235659777865121/2073545183503125000000000000:ℝ),(2315860132967517984310214577971731/2073545183503125000000000000:ℝ),(1769621551147705281940910483830007/2073545183503125000000000000:ℝ),(413542919193602219866355683723397/2073545183503125000000000000:ℝ)],
![(875186989195240722616160167139401/1036772591751562500000000000:ℝ),(2023822131006196629964176106486627/1036772591751562500000000000:ℝ),(288010196137563465831790030531189/207354518350312500000000000:ℝ),(291415838876861421810934213308719/1036772591751562500000000000:ℝ)],
![(933779138947835731984415295347941/2073545183503125000000000000:ℝ),(431573407956320964091583539079711/414709036700625000000000000:ℝ),(383278307534340768086462464859651/518386295875781250000000000:ℝ),(30902532930359398387234745938799/207354518350312500000000000:ℝ)]]
theorem row147_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (291415838876861421810934213308719/989534305547137843200000000000000000:ℝ) row147_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row147_coefficients,Fin.sum_univ_succ]
 ring
theorem row147_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row147_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row147_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row147_pos
