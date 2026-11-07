/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row193_coefficients : Fin 3 → Fin 4 → ℝ := ![![(807582396889940651440628314367629/413853505666727442159803906250:ℝ),(49493177533931733324387584237407279/10346337641668186053995097656250:ℝ),(39630536713134688458628784536109783/10346337641668186053995097656250:ℝ),(10304598451743698503992136907893229/10346337641668186053995097656250:ℝ)],
![(16660637456836866038949900576913981/5173168820834093026997548828125:ℝ),(7278803282481462632254990464187379/1034633764166818605399509765625:ℝ),(24288110310994195222443711558089597/5173168820834093026997548828125:ℝ),(4526830543289031954787695751566683/5173168820834093026997548828125:ℝ)],
![(24104378857245528674120059557944287/10346337641668186053995097656250:ℝ),(54912858050647532059807151877134611/10346337641668186053995097656250:ℝ),(78644916430015382941035982024200847/20692675283336372107990195312500:ℝ),(16958206012874585806334387229570199/20692675283336372107990195312500:ℝ)]]
theorem row193_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4526830543289031954787695751566683/4821742817311048826557317120000000000:ℝ) row193_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row193_coefficients,Fin.sum_univ_succ]
 ring
theorem row193_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row193_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row193_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row193_pos
