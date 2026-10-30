/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11489702103706576867753274221763/3333027506897591279296875:ℝ),(33530193566870391256703599719187/3333027506897591279296875:ℝ),(13041039093730957272224758506089/1333211002759036511718750:ℝ),(7041377442808139649104823220199/2222018337931727519531250:ℝ)],
![(20374188950407189755944192317618/3333027506897591279296875:ℝ),(59299876071279612945339636625502/3333027506897591279296875:ℝ),(2300025105126141199300647487396/133321100275903651171875:ℝ),(6191617126907502769592591375672/1111009168965863759765625:ℝ)],
![(1792693997879285348302225468081/666605501379518255859375:ℝ),(5201554343614886481296374567643/666605501379518255859375:ℝ),(5027441802586471177757189349793/666605501379518255859375:ℝ),(539523851299971552537940500077/222201833793172751953125:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (539523851299971552537940500077/3313713921017029853184000000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ]
 ring
theorem row006_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row006_pos
