/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row161_coefficients : Fin 3 → Fin 4 → ℝ := ![![(101451709548853294405986578318232187357663/1167049872243665993629687500000000:ℝ),(1649227966247304730839801566045865789912019/8169349105705661955407812500000000:ℝ),(1172904180011455835483559434674757674430249/8169349105705661955407812500000000:ℝ),(33404087187719521486187856469223237824553/1167049872243665993629687500000000:ℝ)],
![(4110339645224379190253623112534325752179/23340997444873319872593750000000:ℝ),(1669412136628381971603089189623856056023163/4084674552852830977703906250000000:ℝ),(592945587594974251793359332784335728863159/2042337276426415488851953125000000:ℝ),(5894469587192324278903682630001519192737/102116863821320774442597656250000:ℝ)],
![(107648990319366741403189824729241693233721/1167049872243665993629687500000000:ℝ),(352925933963297826131011863690824998815011/1633869821141132391081562500000000:ℝ),(509475032427310314076914147526910367863621/3267739642282264782163125000000000:ℝ),(525182052460270416651739620791514540815089/16338698211411323910815625000000000:ℝ)]]
theorem row161_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (33404087187719521486187856469223237824553/570304402100624905760637399859200000000000000:ℝ) row161_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row161_coefficients,Fin.sum_univ_succ]
 ring
theorem row161_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row161_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row161_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row161_pos
