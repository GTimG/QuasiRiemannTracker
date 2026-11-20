/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(169211600089921550228466344086/15337260259537587890625:ℝ),(87967453092182472194831836766/3067452051907517578125:ℝ),(41455829172151647185923867453/1704140028837509765625:ℝ),(11386310797597112658624663037/1704140028837509765625:ℝ)],
![(107547441599240364050500424204/5112420086512529296875:ℝ),(4118328446323553296881850556/76304777410634765625:ℝ),(229936667841685909592601752192/5112420086512529296875:ℝ),(61556103537248202752018189144/5112420086512529296875:ℝ)],
![(161715738817188550655535912026/15337260259537587890625:ℝ),(412700758811889416176605087326/15337260259537587890625:ℝ),(113786970195919724213316220958/5112420086512529296875:ℝ),(30125296864352769039626495858/5112420086512529296875:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (15062648432176384519813247929/39035870355528540487680000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row198_coefficients,Fin.sum_univ_succ]
 ring
theorem row198_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row198_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row198_pos
