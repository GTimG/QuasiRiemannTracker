/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3344549236558240240841577319/5925382234484606718750000:ℝ),(75764181711088761767411675599/53328440110361460468750000:ℝ),(3152382658810781860230853753/2666422005518073023437500:ℝ),(4328278336818062532601148833/13332110027590365117187500:ℝ)],
![(94465851524906976503531186/123445463218429306640625:ℝ),(241904121902655936142158293/133321100275903651171875:ℝ),(4693835024356108227737899309/3333027506897591279296875:ℝ),(1184926426815733610716784006/3333027506897591279296875:ℝ)],
![(89653091911386619067921999/370336389655287919921875:ℝ),(1751494149213785037435109711/3333027506897591279296875:ℝ),(1213714338128877808533638474/3333027506897591279296875:ℝ),(261175655353262623334826754/3333027506897591279296875:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (130587827676631311667413377/3033795704056118640000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row035_pos
