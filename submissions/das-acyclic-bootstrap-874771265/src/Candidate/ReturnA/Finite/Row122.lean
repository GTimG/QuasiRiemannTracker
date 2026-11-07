/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row122_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5614586564507689976626784201523856774/4596323892929527208994140625:ℝ),(16506961492769666058006977924519326246/4596323892929527208994140625:ℝ),(3234596323859944171220141211446538049/919264778585905441798828125:ℝ),(5280601440340148145523576252205970773/4596323892929527208994140625:ℝ)],
![(11025175744510070218574636852574762692/4596323892929527208994140625:ℝ),(32394922905538905896748197272047193916/4596323892929527208994140625:ℝ),(31720022993618936205620113010951559856/4596323892929527208994140625:ℝ),(10350265194813151512450162607104128632/4596323892929527208994140625:ℝ)],
![(5425283761945427644619605486060987018/4596323892929527208994140625:ℝ),(3186384164960937450937975020304740374/919264778585905441798828125:ℝ),(15590876857234362594143468136628701386/4596323892929527208994140625:ℝ),(5084234406410154781672429568040986534/4596323892929527208994140625:ℝ)]]
theorem row122_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2542117203205077390836214784020493267/1123047014511259021958939934720000000000:ℝ) row122_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row122_coefficients,Fin.sum_univ_succ]
 ring
theorem row122_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row122_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row122_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row122_pos
