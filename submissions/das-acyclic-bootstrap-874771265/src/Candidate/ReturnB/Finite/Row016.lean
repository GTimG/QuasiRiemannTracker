/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row016_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7386711841662713595604783954202341319/24916163655991804453125000:ℝ),(22047836267843768556707103437542170919/24916163655991804453125000:ℝ),(2741969729009478949972188909171346432/3114520456998975556640625:ℝ),(9185143033154547223947358789101568/31459802595949248046875:ℝ)],
![(27109863005310017017693723070217749/46141043807392230468750:ℝ),(1213720763057448185608137526280857883/692115657110883457031250:ℝ),(5433794900037010366780129745720922112/3114520456998975556640625:ℝ),(1801967188025805649934621369540509696/3114520456998975556640625:ℝ)],
![(164838665850171208728304738777254989/566276446727086464843750:ℝ),(491976650509815915597997735754318701/566276446727086464843750:ℝ),(16314744587179806169792033613627392/18875881557569548828125:ℝ),(81152175054490437072017595872129024/283138223363543232421875:ℝ)]]
theorem row016_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (19812542737912704363285545867219/135118823288217922437120000000000:ℝ) row016_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row016_coefficients,Fin.sum_univ_succ]
 ring
theorem row016_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row016_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row016_pos
