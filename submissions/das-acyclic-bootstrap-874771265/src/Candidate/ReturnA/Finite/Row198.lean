/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(507654643571404262045118243556/46011787588325478515625:ℝ),(263914215814553167913753340436/9202357517665095703125:ℝ),(1119366423170990759875579639342/46011787588325478515625:ℝ),(102483329223209727450643726906/15337262529441826171875:ℝ)],
![(967965879882708906205393603352/46011787588325478515625:ℝ),(2483468274211698086387921967976/46011787588325478515625:ℝ),(2069545736362246387741525796096/46011787588325478515625:ℝ),(184681114011085735852999143824/15337262529441826171875:ℝ)],
![(485166284548374787506985572796/46011787588325478515625:ℝ),(1238159232533950629964484798996/46011787588325478515625:ℝ),(1024139439720222765085812675004/46011787588325478515625:ℝ),(90382163911548974209437816268/15337262529441826171875:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (22595540977887243552359454067/58553814199216782704640000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row198_coefficients,Fin.sum_univ_succ]
 ring
theorem row198_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row198_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row198_pos
