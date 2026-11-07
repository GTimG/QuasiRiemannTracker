/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![![(101423070820963376626162168709/3413020075993715467500000000:ℝ),(9879404884983839862633551261/126408150962730202500000000:ℝ),(76406217108745740901241753989/1137673358664571822500000000:ℝ),(63897790252636923038781546629/3413020075993715467500000000:ℝ)],
![(68136151150477282358905443773/1706510037996857733750000000:ℝ),(695962057091615702094007997/7022675053485011250000000:ℝ),(136301030318431387993460076223/1706510037996857733750000000:ℝ),(470912021275280729913621023/22753467173291436450000000:ℝ)],
![(48501311783966049961648718837/3413020075993715467500000000:ℝ),(809039036293966446888016967/25281630192546040500000000:ℝ),(78811418288318499032355135479/3413020075993715467500000000:ℝ),(17740653587882365954121563771/3413020075993715467500000000:ℝ)]]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17740653587882365954121563771/194162919878753591040000000000:ℝ) row036_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ]
 ring
theorem row036_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row036_pos
