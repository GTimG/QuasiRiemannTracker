/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row133_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1460405484882230349297040806343103/955685805147879929103515625:ℝ),(4057377786632087009866151411604509/955685805147879929103515625:ℝ),(3743669940544922717587890425904709/955685805147879929103515625:ℝ),(1146626791129737951814717320643303/955685805147879929103515625:ℝ)],
![(14340704398274721032266548050800262/4778429025739399645517578125:ℝ),(39641517110951279091446346705851714/4778429025739399645517578125:ℝ),(36366911697937135399257003018939142/4778429025739399645517578125:ℝ),(2213071016954926447086909622777538/955685805147879929103515625:ℝ)],
![(7293185841401276004229792479774997/4778429025739399645517578125:ℝ),(20109782789735162830833941159022469/4778429025739399645517578125:ℝ),(36790904207586326758743834663158419/9556858051478799291035156250:ℝ),(446277168616332429826429929686539/382274322059151971641406250:ℝ)]]
theorem row133_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1106535508477463223543454811388769/456071030929063637692710912000000000:ℝ) row133_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row133_coefficients,Fin.sum_univ_succ]
 ring
theorem row133_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row133_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row133_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row133_pos
