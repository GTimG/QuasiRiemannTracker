/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row211_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1646953610234333431991921884458513491188/2417012448450378685524052734375:ℝ),(289586987976032493738829732430743599172/161134163230025245701603515625:ℝ),(3752742554128080997206018414269446077796/2417012448450378685524052734375:ℝ),(15759399046631152783289638493434131812/36074812663438487843642578125:ℝ)],
![(664367682720446608684455693371998788904/483402489690075737104810546875:ℝ),(2920869941748371667101196193297981093928/805670816150126228508017578125:ℝ),(7571765021164359372030318611302391418208/2417012448450378685524052734375:ℝ),(26308274634344739747271854130854609024/29839659857412082537333984375:ℝ)],
![(1682324211941953708190347738258513475932/2417012448450378685524052734375:ℝ),(493450755591242913713819997425313260156/268556938716708742836005859375:ℝ),(142266964942181215427199567526922368706/89518979572236247612001953125:ℝ),(216492741810546613649578722074933680418/483402489690075737104810546875:ℝ)]]
theorem row211_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3939849761657788195822409623358532953/17628744885907337693427306332160000000000:ℝ) row211_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row211_coefficients,Fin.sum_univ_succ]
 ring
theorem row211_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row211_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row211_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row211_pos
