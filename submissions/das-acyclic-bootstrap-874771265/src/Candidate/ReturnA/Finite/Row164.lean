/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row164_coefficients : Fin 3 → Fin 4 → ℝ := ![![(207519252003781441271942734109343180658994/3545724438240304668145751953125:ℝ),(3746714431352142716937906900357524683599598/31911519944162742013311767578125:ℝ),(1895292962611492621680702588775924229460992/31911519944162742013311767578125:ℝ),(464268763438885640562659000271415399424/911757712690364057523193359375:ℝ)],
![(110277753147167959315271846599881370721153/945526516864081244838867187500:ℝ),(1191354580361811623747845124769068670091913/5105843191066038722129882812500:ℝ),(747218532452047471980622570897203514760192/6382303988832548402662353515625:ℝ),(2399182180257261115172271154542637520896/6382303988832548402662353515625:ℝ)],
![(211669296130291684609636235488172109959677/3630821824758071980181250000000:ℝ),(3806985352144498609970254086825022284800851/32677396422822647821631250000000:ℝ),(14874346147128524445643404386498049176416/255292159553301936106494140625:ℝ),(3050253135880964980825245773973308416/51058431910660387221298828125:ℝ)]]
theorem row164_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2978762828008754864087154076145809/99803270367609358508111544975360000000000:ℝ) row164_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row164_coefficients,Fin.sum_univ_succ]
 ring
theorem row164_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row164_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row164_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row164_pos
