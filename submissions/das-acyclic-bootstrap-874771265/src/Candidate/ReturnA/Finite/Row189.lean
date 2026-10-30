/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row189_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34660868015246931694319473538574871/828912172612105818900000000000000:ℝ),(520084420618728447568991778534094163/7460209553508952370100000000000000:ℝ),(23165959651123242990414425106476017/746020955350895237010000000000000:ℝ),(7231178233790955461163418926419923/3730104776754476185050000000000000:ℝ)],
![(995674824526857939937156871164739/7675112709371350175000000000000:ℝ),(88321904250575990528868877344411959/373010477675447618505000000000000:ℝ),(240745260813071090911213116981808823/1865052388377238092525000000000000:ℝ),(7008860175757595979426117120556121/373010477675447618505000000000000:ℝ)],
![(45077877746087670508924874536581373/414456086306052909450000000000000:ℝ),(821487469949904467670069043152972223/3730104776754476185050000000000000:ℝ),(535014733623645548041254143429143847/3730104776754476185050000000000000:ℝ),(111174268666623931252219285305403981/3730104776754476185050000000000000:ℝ)]]
theorem row189_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7231178233790955461163418926419923/6790448518038370868428800000000000000:ℝ) row189_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row189_coefficients,Fin.sum_univ_succ]
 ring
theorem row189_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row189_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row189_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row189_pos
