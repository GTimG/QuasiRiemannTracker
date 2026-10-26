/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row210_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5044375230639600331267455235159883/51752311518972985449029296875:ℝ), (2141752690487715276622309858930627/10350462303794597089805859375:ℝ), (6573563492378294194101170904853696/51752311518972985449029296875:ℝ), (906098049468784918540949821922944/51752311518972985449029296875:ℝ)],
![(217611423997084806387497244816836/976458707905150668849609375:ℝ), (25248385302792475937315119472358532/51752311518972985449029296875:ℝ), (3299928915940390842711392093509888/10350462303794597089805859375:ℝ), (2778217237856712926993024064233216/51752311518972985449029296875:ℝ)],
![(274244113993145139990591953792012/2070092460758919417961171875:ℝ), (15618208296910796322798393311962172/51752311518972985449029296875:ℝ), (10982559783067359427716417189583744/51752311518972985449029296875:ℝ), (2217077068371817272985304628671872/51752311518972985449029296875:ℝ)]]
theorem row210_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7078891011474882176101170483773/24118325245919385417867264000000000:ℝ) row210_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row210_coefficients,Fin.sum_univ_succ]
 ring
theorem row210_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row210_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row210_coefficients]
#print axioms row210_identity
#print axioms row210_pos
end
end LewkoStage2Return.C30
