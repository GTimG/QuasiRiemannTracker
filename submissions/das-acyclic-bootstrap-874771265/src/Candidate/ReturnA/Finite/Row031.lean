/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1090529477336797059872235071089393499/485690726139905753261718750:ℝ),(3239087234321947216311365842362467563/485690726139905753261718750:ℝ),(6413444124522178981880306960704042333/971381452279811506523437500:ℝ),(141088551840977836592405912252192947/64758763485320767101562500:ℝ)],
![(1050604480921789247746895258629066769/242845363069952876630859375:ℝ),(3119648716751276152077056345521788631/242845363069952876630859375:ℝ),(617524148250612348908030325661248106/48569072613990575326171875:ℝ),(339525444964919796147760331512839556/80948454356650958876953125:ℝ)],
![(1011385138533311296588529844140171789/485690726139905753261718750:ℝ),(3002327884531936547098275289449064399/485690726139905753261718750:ℝ),(2970637783309042652791841396505501581/485690726139905753261718750:ℝ),(326564954207454183084261244148869657/161896908713301917753906250:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (326564954207454183084261244148869657/2472326855989792629074165760000000000:ℝ) row031_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row031_coefficients,Fin.sum_univ_succ]
 ring
theorem row031_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row031_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row031_pos
