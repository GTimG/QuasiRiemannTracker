/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row152_coefficients : Fin 3 → Fin 4 → ℝ := ![![(183748602939012561724103255851359227268509/32677396422822647821631250000000000:ℝ),(433244706902161831467428829132709976402407/32677396422822647821631250000000000:ℝ),(63523462161555361520538353395120312483351/6535479284564529564326250000000000:ℝ),(3243434335459256545041925357974175632517/1556066496324887991506250000000000:ℝ)],
![(35391334125622727625961222349482930748353/3267739642282264782163125000000000:ℝ),(11695561778751745936955167742287215457373/466819948897466397451875000000000:ℝ),(290253293716394121438205658733254736392549/16338698211411323910815625000000000:ℝ),(2755046532772092608155550745775073172679/778033248162443995753125000000000:ℝ)],
![(182933972839411175303051354641905042366473/32677396422822647821631250000000000:ℝ),(423524576029551811410953707284696968082559/32677396422822647821631250000000000:ℝ),(150371509219257710162318669496246708687133/16338698211411323910815625000000000:ℝ),(143197249895922069367585868518445143829/77803324816244399575312500000000:ℝ)]]
theorem row152_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2755046532772092608155550745775073172679/23762683420859371073359891660800000000000000:ℝ) row152_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row152_coefficients,Fin.sum_univ_succ]
 ring
theorem row152_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row152_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row152_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row152_pos
