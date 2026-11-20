/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row155_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3025768780863568023789300772654785488321/2552888802561516771240234375000:ℝ),(6881808967055442029258464311952079979827/2552888802561516771240234375000:ℝ),(117448536653057024230320606500916326464/63822220064037919281005859375:ℝ),(105236240343881219158458234202091012288/319111100320189596405029296875:ℝ)],
![(22162005392331671603226730070630064483523/10211555210246067084960937500000:ℝ),(48789420052698672523889623982333901433177/10211555210246067084960937500000:ℝ),(974576659947928553251831839915807223744/319111100320189596405029296875:ℝ),(142467093837049160660676912395847743872/319111100320189596405029296875:ℝ)],
![(164902927985516016323183679699296329722569/163384883363937073359375000000000:ℝ),(352057281981379010617654935523921946455883/163384883363937073359375000000000:ℝ),(16418716014097619799579375953187251132/12764444012807583856201171875:ℝ),(44930614315833663486624035207670456128/319111100320189596405029296875:ℝ)]]
theorem row155_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (702040848684900991978500550119850877/77970303412098243986718720000000000000000:ℝ) row155_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row155_coefficients,Fin.sum_univ_succ]
 ring
theorem row155_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row155_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row155_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row155_pos
