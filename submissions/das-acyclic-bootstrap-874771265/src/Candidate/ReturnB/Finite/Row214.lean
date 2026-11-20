/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row214_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16357755469339510976487889375376071583/161134163230025245701603515625:ℝ),(194873345748036422885096404134997649879/805670816150126228508017578125:ℝ),(5384871884927546796258755494956364544/29839659857412082537333984375:ℝ),(32303053822729151145508616344727988224/805670816150126228508017578125:ℝ)],
![(55120435040599402879382089718712363712/268556938716708742836005859375:ℝ),(394354088160635002945821629876340790592/805670816150126228508017578125:ℝ),(28515375947483060599998970951586418688/77968143498399312436259765625:ℝ),(39394929073461811617416086775213576192/483402489690075737104810546875:ℝ)],
![(40386376086833369180247048839656448/387901211434822449931640625:ℝ),(66801710855740567883109815514044394496/268556938716708742836005859375:ℝ),(450558705751141781141430959253565118464/2417012448450378685524052734375:ℝ),(100978913100293663950600177947064895488/2417012448450378685524052734375:ℝ)]]
theorem row214_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (15772975499379468332767879074574213/96120272408511688269826621440000000000:ℝ) row214_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row214_coefficients,Fin.sum_univ_succ]
 ring
theorem row214_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row214_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row214_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row214_pos
