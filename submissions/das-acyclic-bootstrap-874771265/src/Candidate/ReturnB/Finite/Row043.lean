/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(95912075885545872371439949283/474319882265625000000:ℝ),(158207058340095965258879554423/263511045703125000000:ℝ),(14678206803648890790190951303/24704160534667968750:ℝ),(14525147109911224699550471303/74112481604003906250:ℝ)],
![(620397529630441971773550822209/1581066274218750000000:ℝ),(5524308905136558705321608968387/4743198822656250000000:ℝ),(8539520081045569425046465801/7411248160400390625:ℝ),(938633612304131063556657089/2470416053466796875:ℝ)],
![(7221349822555874196618285919079/37945590581250000000000:ℝ),(4285397004220204521677145606523/7589118116250000000000:ℝ),(41388578780606992462048263067/74112481604003906250:ℝ),(13643197533448499470314977689/74112481604003906250:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (13643197533448499470314977689/141471415428710400000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ]
 ring
theorem row043_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row043_pos
