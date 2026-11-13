/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row015_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7398097146293210115524623680166932464/3114520456998975556640625:ℝ),(22137967907678969467808819613400572656/3114520456998975556640625:ℝ),(4416339872664639686421369186319212544/622904091399795111328125:ℝ),(7341828586684252199334459305862422528/3114520456998975556640625:ℝ)],
![(14661806459777355637053397398055784692/3114520456998975556640625:ℝ),(43873056550560998106073286357871308596/3114520456998975556640625:ℝ),(1326084965722867682555473240076337152/94379407787847744140625:ℝ),(179624120337826141567401258806525952/38450869839493525390625:ℝ)],
![(29055985856993871698670333964599687287/12458081827995902226562500:ℝ),(17388760102798235665237698424372502587/2491616365599180445312500:ℝ),(21679966023230653493395078291806416896/3114520456998975556640625:ℝ),(655273849411525448350175299896172544/283138223363543232421875:ℝ)]]
theorem row015_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (79989483570742852581808508288107/540475293152871689748480000000000:ℝ) row015_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row015_coefficients,Fin.sum_univ_succ]
 ring
theorem row015_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row015_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row015_pos
