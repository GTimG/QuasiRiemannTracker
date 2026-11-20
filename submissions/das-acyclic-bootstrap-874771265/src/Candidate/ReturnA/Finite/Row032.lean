/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row032_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2147744741963738517675947407920680723/971381452279811506523437500:ℝ),(6378774934213039217805801314406682451/971381452279811506523437500:ℝ),(1578646673744600499526036054929213952/242845363069952876630859375:ℝ),(104177808489594508892916678942792704/48569072613990575326171875:ℝ)],
![(1034284567069294872838210356607411927/242845363069952876630859375:ℝ),(614192392927820207860864485026310251/48569072613990575326171875:ℝ),(3039206466999748288420609852965730304/242845363069952876630859375:ℝ),(1002528898901126670187788237566590976/242845363069952876630859375:ℝ)],
![(99540309479689803364771309451550223/48569072613990575326171875:ℝ),(1477328044474369547954824542190416011/242845363069952876630859375:ℝ),(1461619899643861490074551289496522752/242845363069952876630859375:ℝ),(481993315223913532428927185188857856/242845363069952876630859375:ℝ)]]
theorem row032_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (235348298449176529506312102142997/1810786271476898898247680000000000:ℝ) row032_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row032_coefficients,Fin.sum_univ_succ]
 ring
theorem row032_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row032_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row032_pos
