/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row098_coefficients : Fin 3 → Fin 4 → ℝ := ![![(58415816726858353513321263324194/38227191375766136958984375:ℝ),(162293994120267774442313564310182/38227191375766136958984375:ℝ),(149745768620000479493151646997782/38227191375766136958984375:ℝ),(45864757319585660083493721011794/38227191375766136958984375:ℝ)],
![(573624020158207313019631609815476/191135956878830684794921875:ℝ),(1585649177691642999544829330832572/191135956878830684794921875:ℝ),(1454665897675669318626166797557716/191135956878830684794921875:ℝ),(88522196823735389610796002808124/38227191375766136958984375:ℝ)],
![(291725206912680476253860488156006/191135956878830684794921875:ℝ),(804385140608594104471131922375462/191135956878830684794921875:ℝ),(735812409922281850499813694109481/191135956878830684794921875:ℝ),(8925474172560038526314920083101/7645438275153227391796875:ℝ)]]
theorem row098_identity (δ p : ℝ) : rowMargin .oldSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (22130549205933847402699000702031/9121363154269378065727488000000000:ℝ) row098_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row098_coefficients,Fin.sum_univ_succ]
 ring
theorem row098_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .P δ p := by
 rw [row098_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row098_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row098_pos
