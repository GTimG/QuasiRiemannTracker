/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row014_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2227965249269300407253979758399958634657/934362267224721174492187500:ℝ),(6666965592487908957529475501774626825187/934362267224721174492187500:ℝ),(6650051946983892733242715840685151541603/934362267224721174492187500:ℝ),(245672399909925400611325131812275927897/103818029691635686054687500:ℝ)],
![(2207764288503768386414123191074885711841/467181133612360587246093750:ℝ),(6606405293221969963018703762644534168163/467181133612360587246093750:ℝ),(6589534256845318452314140420959314047603/467181133612360587246093750:ℝ),(34776083293985021068887127059756596687/7415573549402549003906250:ℝ)],
![(87505978532466593981395845347960627329/37374490688988846979687500:ℝ),(935157630202498293731138635994832990677/133480323889245882070312500:ℝ),(6529274994538163716582062166420105489753/934362267224721174492187500:ℝ),(26800259775258974465504102801492780719/11535336632403965117187500:ℝ)]]
theorem row014_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (241202337977330770189536925213435026471/1623454304977741546751430492160000000000:ℝ) row014_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row014_coefficients,Fin.sum_univ_succ]
 ring
theorem row014_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row014_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row014_pos
