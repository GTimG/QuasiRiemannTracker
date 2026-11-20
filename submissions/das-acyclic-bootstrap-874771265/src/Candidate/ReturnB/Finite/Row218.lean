/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row218_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4138597610092045080930831455885050976/483402489690075737104810546875:ℝ),(10416996322698488910081495851977322528/483402489690075737104810546875:ℝ),(313223211475639039044600722159455264/17903795914447249522400390625:ℝ),(726159730969262868330510854904340192/161134163230025245701603515625:ℝ)],
![(2917615692918376917220885618487246336/161134163230025245701603515625:ℝ),(36906643958101769797475456387382151744/805670816150126228508017578125:ℝ),(30181596503716822830704706778063270448/805670816150126228508017578125:ℝ),(7862522595419530417455101479992350384/805670816150126228508017578125:ℝ)],
![(4803578595463273765439629966391660932/483402489690075737104810546875:ℝ),(61458055324714719957177028924180530392/2417012448450378685524052734375:ℝ),(17022013976203466675091242444355996443/805670816150126228508017578125:ℝ),(168211085104647041017364643191865137/29839659857412082537333984375:ℝ)]]
theorem row218_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (22692491592789464635328464215760631/76896217926809350615861297152000000000:ℝ) row218_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row218_coefficients,Fin.sum_univ_succ]
 ring
theorem row218_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row218_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row218_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row218_pos
