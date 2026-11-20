/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row116_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4056243596131647757260823151042/2406731869977642861328125:ℝ),(1241264141840583626715771402145976/262333773827563071884765625:ℝ),(2317304073598571235444227282483111/524667547655126143769531250:ℝ),(143802263572675894361507331898663/104933509531025228753906250:ℝ)],
![(842359521096020203527554832066808/262333773827563071884765625:ℝ),(2349041053344658557945633833617816/262333773827563071884765625:ℝ),(2176264293228314229570979429499708/262333773827563071884765625:ℝ),(26782233554524983583463079617948/10493350953102522875390625:ℝ)],
![(83115807218786299885753954192996/52466754765512614376953125:ℝ),(230675704472207553821292869882188/52466754765512614376953125:ℝ),(212554082198313860535882866260388/52466754765512614376953125:ℝ),(64991351037887208119678325571196/52466754765512614376953125:ℝ)]]
theorem row116_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16247837759471802029919581392799/6259527662364689650679808000000000:ℝ) row116_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row116_coefficients,Fin.sum_univ_succ]
 ring
theorem row116_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row116_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row116_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row116_pos
