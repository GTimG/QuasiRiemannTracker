/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row161_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14202399561333011592829230887394952877777/163384883363937073359375000000000:ℝ),(32982191615287143513135487288426308059771/163384883363937073359375000000000:ℝ),(23455866228984413602507021265371461656809/163384883363937073359375000000000:ℝ),(935176554075746492375913277635841919963/32676976672787414671875000000000:ℝ)],
![(14385342198607977329374508672496356891621/81692441681968536679687500000000:ℝ),(33385856944588432808438353077391881117203/81692441681968536679687500000000:ℝ),(11857795157219592842259769005936247203161/40846220840984268339843750000000:ℝ),(117872042747534797314156865938298981081/2042311042049213416992187500000:ℝ)],
![(15069997558858761278506189689573447961823/163384883363937073359375000000000:ℝ),(35290166360481029026161425736481117478399/163384883363937073359375000000000:ℝ),(50942959001313098177340891290586025586117/326769766727874146718750000000000:ℝ),(2100445742044329322466267949168722623093/65353953345574829343750000000000:ℝ)]]
theorem row161_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (935176554075746492375913277635841919963/15968318138797720368479993856000000000000000:ℝ) row161_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row161_coefficients,Fin.sum_univ_succ]
 ring
theorem row161_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row161_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row161_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row161_pos
