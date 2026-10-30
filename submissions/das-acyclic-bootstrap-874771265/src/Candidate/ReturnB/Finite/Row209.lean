/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row209_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6570689451967046409933568364417881816/805670816150126228508017578125:ℝ),(5523355546995489808421299081563244948/268556938716708742836005859375:ℝ),(2697938599736004868464490715028622883/161134163230025245701603515625:ℝ),(3490080047803392072706357737019698887/805670816150126228508017578125:ℝ)],
![(39909104736655600461528334236815747176/2417012448450378685524052734375:ℝ),(100324158365435526612878516066670263416/2417012448450378685524052734375:ℝ),(27099969490488556798548412607062099768/805670816150126228508017578125:ℝ),(6961134666829177816230112083568927688/805670816150126228508017578125:ℝ)],
![(21143682014755401705266651977636966228/2417012448450378685524052734375:ℝ),(53437063506377973452244963354521746684/2417012448450378685524052734375:ℝ),(4848579493566311019206509065129066076/268556938716708742836005859375:ℝ),(1260343325426013258396684169086312692/268556938716708742836005859375:ℝ)]]
theorem row209_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (870141833353647227028764010446115961/3075848717072374024634451886080000000000:ℝ) row209_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row209_coefficients,Fin.sum_univ_succ]
 ring
theorem row209_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row209_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row209_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row209_pos
