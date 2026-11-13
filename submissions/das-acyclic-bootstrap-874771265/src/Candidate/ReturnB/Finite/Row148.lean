/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![![(77350783248247611737085501623/57598114570312500000000:ℝ),(7797912820575801037012571629547/2591915155664062500000000:ℝ),(163732708445930827868870290889/80997348614501953125000:ℝ),(28822471745785249467503914123/80997348614501953125000:ℝ)],
![(1411279757766503009986472843863/575981145703125000000000:ℝ),(27158676719982604271124668440847/5183830311328125000000000:ℝ),(25881134906108971687932283039/8099734861450195312500:ℝ),(3291824124727601092234762967/8099734861450195312500:ℝ)],
![(5412337108011330079807635138091/4607849165625000000000000:ℝ),(20161741319328949496155511219431/8294128498125000000000000:ℝ),(222336862175362157837630840779/161994697229003906250000:ℝ),(9415164242870968054540342549/80997348614501953125000:ℝ)]]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (9415164242870968054540342549/154613761494220800000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ]
 ring
theorem row148_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row148_pos
