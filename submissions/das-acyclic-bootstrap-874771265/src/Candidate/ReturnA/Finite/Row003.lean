/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(337164872531341955194637994413/53328440110361460468750000:ℝ),(188276019205365794239824399419/10665688022072292093750000:ℝ),(874022806494987067431749833151/53328440110361460468750000:ℝ),(89925297852147604183255276823/17776146703453820156250000:ℝ)],
![(241980394890155741541510385853/26664220055180730234375000:ℝ),(660964192893031560925470061159/26664220055180730234375000:ℝ),(599269871236185873637818039059/26664220055180730234375000:ℝ),(60079513022908065312536121251/8888073351726910078125000:ℝ)],
![(164409841293001699599018708293/53328440110361460468750000:ℝ),(435074933175070199855812476823/53328440110361460468750000:ℝ),(380564580753356501259601451717/53328440110361460468750000:ℝ),(36609395874803071176144227729/17776146703453820156250000:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (36609395874803071176144227729/258883900079455457280000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ]
 ring
theorem row003_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row003_pos
