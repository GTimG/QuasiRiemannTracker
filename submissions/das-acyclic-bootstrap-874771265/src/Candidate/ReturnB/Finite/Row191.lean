/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row191_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2368848530454997384537729576155083/220721834077483396946619375000000:ℝ),(1589947231160810404990138403225747/73573944692494465648873125000000:ℝ),(2971348744511936856686367366666083/220721834077483396946619375000000:ℝ),(21623788635207160553966969325757/8828873363099335877864775000000:ℝ)],
![(4238798541211785987010101004746347/110360917038741698473309687500000:ℝ),(83483106514758730089187575708851/1114756737765067661346562500000:ℝ),(1614744064204768113253067764880219/36786972346247232824436562500000:ℝ),(151736291531265604626143860842151/22072183407748339694661937500000:ℝ)],
![(13171847242448043291774292433337611/220721834077483396946619375000000:ℝ),(10024913074168895526958454073190219/73573944692494465648873125000000:ℝ),(22604983827330711937514409710129881/220721834077483396946619375000000:ℝ),(124067741885661613306562442753263/4904929646166297709924875000000:ℝ)]]
theorem row191_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21623788635207160553966969325757/4018118366139431083970457600000000:ℝ) row191_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row191_coefficients,Fin.sum_univ_succ]
 ring
theorem row191_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row191_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row191_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row191_pos
