/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row179_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8057849781643797484946357973823247338711/130707906691149658687500000000000:ℝ),(16117064143700154560547982376804051837887/130707906691149658687500000000000:ℝ),(80316273509769197392825345129073776307/1276444401280758385620117187500:ℝ),(401698648557361845994280242446828173/319111100320189596405029296875:ℝ)],
![(1288273769686177515004896015693161602873/10211555210246067084960937500000:ℝ),(2596501514739412281072863005410237231889/10211555210246067084960937500000:ℝ),(42310379210800337672411066929880224642/319111100320189596405029296875:ℝ),(1425135807530455412698489269057060454/319111100320189596405029296875:ℝ)],
![(41417117883969026017455817139876903729/638222200640379192810058593750:ℝ),(84315284401317571083460861801167047237/638222200640379192810058593750:ℝ),(22594402197032987600726201781183643481/319111100320189596405029296875:ℝ),(1143745921827245472710542729952634227/319111100320189596405029296875:ℝ)]]
theorem row179_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (401698648557361845994280242446828173/77970303412098243986718720000000000000000:ℝ) row179_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row179_coefficients,Fin.sum_univ_succ]
 ring
theorem row179_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row179_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row179_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row179_pos
