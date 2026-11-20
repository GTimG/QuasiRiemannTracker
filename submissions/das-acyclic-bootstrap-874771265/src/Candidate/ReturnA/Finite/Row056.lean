/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row056_coefficients : Fin 3 → Fin 4 → ℝ := ![![(522800994932893365992845262697766314643/124581635629962823265625000000:ℝ),(4658669906216960084907602330688418683833/373744906889888469796875000000:ℝ),(72067694022743726078127337466150423704/5839764170154507340576171875:ℝ),(23782268150019499726302832503726677768/5839764170154507340576171875:ℝ)],
![(1028560543313029638579468057528637211291/124581635629962823265625000000:ℝ),(1832860849832293810881040989907439011421/74748981377977693959375000000:ℝ),(47249838602832392503676615245149224144/1946588056718169113525390625:ℝ),(46771026798031474435936227736208868944/5839764170154507340576171875:ℝ)],
![(2023425574832119778158704749959276396387/498326542519851293062500000000:ℝ),(2575145324605512267823509049039243691087/213568518222793411312500000000:ℝ),(69695389573831917783001873249700181512/5839764170154507340576171875:ℝ),(2554808077644725653058728595280542456/648862685572723037841796875:ℝ)]]
theorem row056_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (319351009705590706632341074410067807/4954389358452580403904512000000000000:ℝ) row056_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row056_coefficients,Fin.sum_univ_succ]
 ring
theorem row056_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row056_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row056_pos
