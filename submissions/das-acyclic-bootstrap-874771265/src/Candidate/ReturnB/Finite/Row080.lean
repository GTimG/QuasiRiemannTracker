/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row080_coefficients : Fin 3 → Fin 4 → ℝ := ![![(133192532181844944873218453/2333278974199218750:ℝ),(387836651460795914028758933/2333278974199218750:ℝ),(188128960546642448118223616/1166639487099609375:ℝ),(60806900907166963540453376/1166639487099609375:ℝ)],
![(127904381219515752846631814/1166639487099609375:ℝ),(371644594385596675936221062/1166639487099609375:ℝ),(359741571609437834161656832/1166639487099609375:ℝ),(116001358443356911072067584/1166639487099609375:ℝ)],
![(495613894246985562617234/9333115896796875:ℝ),(179649838704175435005277258/1166639487099609375:ℝ),(173528916465768275837090816/1166639487099609375:ℝ),(55830814542466036158967808/1166639487099609375:ℝ)]]
theorem row080_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (13630569956656747109123/4349547259822080000000000:ℝ) row080_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row080_coefficients,Fin.sum_univ_succ]
 ring
theorem row080_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row080_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row080_pos
