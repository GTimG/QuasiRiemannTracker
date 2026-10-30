/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row195_coefficients : Fin 3 → Fin 4 → ℝ := ![![(125912642276502218615961344958416921/4598371543280904103054570312500:ℝ),(59897077482658289943891278195819171/919674308656180820610914062500:ℝ),(113126523471596289896970409772174461/2299185771640452051527285156250:ℝ),(1461946676269334775542032419928333/127732542868914002862626953125:ℝ)],
![(71653274751302380857660965693773043/1379511462984271230916371093750:ℝ),(812476657508822482771238234364092533/6897557314921356154581855468750:ℝ),(188902131183058969672306850464725557/2299185771640452051527285156250:ℝ),(12480967214204667551579087867938817/766395257213484017175761718750:ℝ)],
![(40234717451540279768745746558505397/1254101329985701119014882812500:ℝ),(1031529550318464764068502903700852101/13795114629842712309163710937500:ℝ),(251167587176878194392802511783112867/4598371543280904103054570312500:ℝ),(18263233085453985720953296879671763/1532790514426968034351523437500:ℝ)]]
theorem row195_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12480967214204667551579087867938817/22858628927370985722143047680000000000:ℝ) row195_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row195_coefficients,Fin.sum_univ_succ]
 ring
theorem row195_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row195_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row195_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row195_pos
