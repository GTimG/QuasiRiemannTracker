/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row103_coefficients : Fin 3 → Fin 4 → ℝ := ![![(234449957503741544724917084982899/1049335095310252287539062500:ℝ),(120172606924107326564182991586631/209867019062050457507812500:ℝ),(126091952984564549567413301185072/262333773827563071884765625:ℝ),(34473061792998518418744575135008/262333773827563071884765625:ℝ)],
![(119662314382416347139367796814781/262333773827563071884765625:ℝ),(305349313691467256084854391267149/262333773827563071884765625:ℝ),(4633322277364497712359603170816/4769704978682964943359375:ℝ),(69112994320084112782603611192512/262333773827563071884765625:ℝ)],
![(2518743335140542945538764334571/10493350953102522875390625:ℝ),(160777682634475969307784382882979/262333773827563071884765625:ℝ),(134275319239369589130329934147808/262333773827563071884765625:ℝ),(36449074846024532652987628379104/262333773827563071884765625:ℝ)]]
theorem row103_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1077283181031203700585767972969/489025598622241378959360000000000:ℝ) row103_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row103_coefficients,Fin.sum_univ_succ]
 ring
theorem row103_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row103_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row103_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row103_pos
