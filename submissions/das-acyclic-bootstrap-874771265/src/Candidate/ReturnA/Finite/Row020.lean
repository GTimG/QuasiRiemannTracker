/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row020_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44567805103298816676296953155025247/18687245344494423489843750:ℝ),(236413689228663162390700319671241981/33370080972311470517578125:ℝ),(13108516644172115321570324684051107547/1868724534449442348984375000:ℝ),(206006188342920179503173506153051491/88986882592830588046875000:ℝ)],
![(214983056085740390243827444717686064/46718113361236058724609375:ℝ),(3192282789896182477299782528994218152/233590566806180293623046875:ℝ),(3159951770394776218279147382379419594/233590566806180293623046875:ℝ),(49646862211488608959951155451125322/11123360324103823505859375:ℝ)],
![(103630775988156633410991917955149684/46718113361236058724609375:ℝ),(307679138460758545701720372458483452/46718113361236058724609375:ℝ),(304479226200412013748442067575892852/46718113361236058724609375:ℝ),(4782421327766122516108326812979004/2224672064820764701171875:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1195605331941530629027081703244751/8493238900204423549550592000000000:ℝ) row020_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row020_coefficients,Fin.sum_univ_succ]
 ring
theorem row020_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row020_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row020_pos
