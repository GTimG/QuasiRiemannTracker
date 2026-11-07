/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row216_coefficients : Fin 3 → Fin 4 → ℝ := ![![(41656169554632114569401927159076111/1379511462984271230916371093750:ℝ),(95346896105659896878195108204245733/1379511462984271230916371093750:ℝ),(22514739075625626263061857123031461/459837154328090410305457031250:ℝ),(512403338327644221208873079126843/51093017147565601145050781250:ℝ)],
![(9275503958458376275220697319730653/127732542868914002862626953125:ℝ),(195420308977706875013202625229869483/1149592885820226025763642578125:ℝ),(28741284675007548735111423254870192/229918577164045205152728515625:ℝ),(10577183010539322402820200692769118/383197628606742008587880859375:ℝ)],
![(344489901625304708378646814510614557/6897557314921356154581855468750:ℝ),(848303572108288839530438014312965533/6897557314921356154581855468750:ℝ),(89858934899569509382747904853019981/919674308656180820610914062500:ℝ),(37781290664604630899314120580205307/1532790514426968034351523437500:ℝ)]]
theorem row216_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (512403338327644221208873079126843/761954297579032857404768256000000000:ℝ) row216_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row216_coefficients,Fin.sum_univ_succ]
 ring
theorem row216_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row216_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row216_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row216_pos
