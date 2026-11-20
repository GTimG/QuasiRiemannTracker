/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row153_coefficients : Fin 3 → Fin 4 → ℝ := ![![(436248750821767639930427544240405735747679/4668199488974663974518750000000000:ℝ),(1469745720895124422859634183655372897922063/6535479284564529564326250000000000:ℝ),(1111001005811690963770971229875249571971823/6535479284564529564326250000000000:ℝ),(1259981337135273582415734996075051020482553/32677396422822647821631250000000000:ℝ)],
![(82561227258556754191976312570969763535091/466819948897466397451875000000000:ℝ),(6829198383543691731041861370570596178528907/16338698211411323910815625000000000:ℝ),(715496817739106940464033327730625366278581/2334099744487331987259375000000000:ℝ),(213777094655922306818388534699091246829869/3267739642282264782163125000000000:ℝ)],
![(403698392191804207175316571152322271532967/4668199488974663974518750000000000:ℝ),(944257373405697288705754549124777507887213/4668199488974663974518750000000000:ℝ),(680169723155482971664462904038752854655383/4668199488974663974518750000000000:ℝ),(139605412528441878776530161719522149551137/4668199488974663974518750000000000:ℝ)]]
theorem row153_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (139605412528441878776530161719522149551137/2281217608402499623042549599436800000000000000:ℝ) row153_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row153_coefficients,Fin.sum_univ_succ]
 ring
theorem row153_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row153_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row153_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row153_pos
