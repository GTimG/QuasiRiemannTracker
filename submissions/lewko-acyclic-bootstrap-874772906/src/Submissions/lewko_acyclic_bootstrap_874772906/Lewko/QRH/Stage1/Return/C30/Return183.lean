/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row183_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1544883548623824330753585908192941/51752311518972985449029296875:ℝ), (748697024905051758244430701459231/10350462303794597089805859375:ℝ), (2908909575676906879946745260942062/51752311518972985449029296875:ℝ), (236580931966009180550922191967116/17250770506324328483009765625:ℝ)],
![(581094717278917450205632202925802/10350462303794597089805859375:ℝ), (6728429675123554277491826569617862/51752311518972985449029296875:ℝ), (4864807368556511043231078114024194/51752311518972985449029296875:ℝ), (346865090403666614607351530095114/17250770506324328483009765625:ℝ)],
![(1750824632028558137842508274166369/51752311518972985449029296875:ℝ), (4131948763587216930089809408197107/51752311518972985449029296875:ℝ), (3079746998059111949658910346832607/51752311518972985449029296875:ℝ), (232641694645235464888062706350623/17250770506324328483009765625:ℝ)]]
theorem row183_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (173432545201833307303675765047557/257262135956473444457250816000000000:ℝ) row183_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row183_coefficients,Fin.sum_univ_succ]
 ring
theorem row183_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row183_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row183_coefficients]
#print axioms row183_identity
#print axioms row183_pos
end
end LewkoStage1Return.C30
