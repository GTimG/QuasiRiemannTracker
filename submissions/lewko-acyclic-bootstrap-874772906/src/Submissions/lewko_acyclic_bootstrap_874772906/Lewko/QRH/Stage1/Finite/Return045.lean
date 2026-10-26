/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row045_coefficients : Fin 3 → Fin 4 → ℝ := ![![(558515603933251356922110638521838481814/491162038347871069417880859375:ℝ),(31536209638636925496196447717114657672226/9332078728609550318939736328125:ℝ),(31238232053538239943088085041220728584704/9332078728609550318939736328125:ℝ),(10313817008429391995761334612271002066944/9332078728609550318939736328125:ℝ)],
![(20556613701632044576902725793112055266616/9332078728609550318939736328125:ℝ),(3214519079633648149505985459962251975912/491162038347871069417880859375:ℝ),(60484317234999667395109309168527053355008/9332078728609550318939736328125:ℝ),(6655021519832771425047808532452107026432/3110692909536516772979912109375:ℝ)],
![(20951727734987208786859323721382104984/19646481533914842776715234375:ℝ),(1555861704548700651288016135575305154008/491162038347871069417880859375:ℝ),(513469539774059646821536963971841206272/163720679449290356472626953125:ℝ),(508340003713183296516864724374771089408/491162038347871069417880859375:ℝ)]]
theorem row045_identity (δ p : ℝ) : rowMargin .oldPeak .weakC7 δ p =
 Record12518109.Bernstein.bsum 2 3 (31026611554759722687796919212327337/457796200464584226209710080000000000:ℝ) row045_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row045_coefficients,Fin.sum_univ_succ]
 ring
theorem row045_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .weakC7 δ p := by
 rw [row045_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_coefficients]
#print axioms row045_identity
#print axioms row045_pos
end
end LewkoStage1Finite
