/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row080_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1564210804001380204424301733582130867422/36725025273689068814410716796875:ℝ),(4534468845757564986450195467699298511582/36725025273689068814410716796875:ℝ),(4378924699855652765344882447970501984768/36725025273689068814410716796875:ℝ),(1408656959516470292947495807603334340608/36725025273689068814410716796875:ℝ)],
![(2982840806489249093992105080903848781512/36725025273689068814410716796875:ℝ),(8625943286007179829807957706095732788936/36725025273689068814410716796875:ℝ),(8308733521990262722961963312059340855296/36725025273689068814410716796875:ℝ),(2665611121058607001518179311867456847872/36725025273689068814410716796875:ℝ)],
![(286662216692291345969414057426994860696/7345005054737813762882143359375:ℝ),(4135269289226097121893708977008908932344/36725025273689068814410716796875:ℝ),(3973356891588699457947683881827683207168/36725025273689068814410716796875:ℝ),(1271388455908902992200215566953748578304/36725025273689068814410716796875:ℝ)]]
theorem row080_identity (δ p : ℝ) : rowMargin .oldSwitch .weakC7 δ p =
 Record12518109.Bernstein.bsum 2 3 (77599393060846129895032688412704381/34230204534563368018790694912000000000:ℝ) row080_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row080_coefficients,Fin.sum_univ_succ]
 ring
theorem row080_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .weakC7 δ p := by
 rw [row080_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_coefficients]
#print axioms row080_identity
#print axioms row080_pos
end
end LewkoStage1Finite
