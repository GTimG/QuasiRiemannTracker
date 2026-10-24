/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row153_coefficients : Fin 3 → Fin 4 → ℝ := ![![(61071447963262779744896389724905143422897/653539533455748293437500000000000:ℝ),(146965011617940137357183783528245085875091/653539533455748293437500000000000:ℝ),(111091106201014043522806448384191502525299/653539533455748293437500000000000:ℝ),(5039363137371564888011076873000642014621/130707906691149658687500000000000:ℝ)],
![(57789516728556096990386275009505263027409/326769766727874146718750000000000:ℝ),(136574520242414839159033591723118071674707/326769766727874146718750000000000:ℝ),(100160681736732401273749388274839748425563/326769766727874146718750000000000:ℝ),(4274988359890857259900144294823485455653/65353953345574829343750000000000:ℝ)],
![(56514436385752687086221773222008130857353/653539533455748293437500000000000:ℝ),(132186605213254768650564227398485710689379/653539533455748293437500000000000:ℝ),(95214917675501124313245891713165936874721/653539533455748293437500000000000:ℝ),(3908400546959567218119361305476007033539/130707906691149658687500000000000:ℝ)]]
theorem row153_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3908400546959567218119361305476007033539/63873272555190881473919975424000000000000000:ℝ) row153_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row153_coefficients,Fin.sum_univ_succ]
 ring
theorem row153_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row153_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row153_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row153_pos
