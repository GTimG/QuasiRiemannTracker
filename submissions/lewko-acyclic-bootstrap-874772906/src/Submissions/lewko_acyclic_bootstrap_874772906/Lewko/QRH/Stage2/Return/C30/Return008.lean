/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(177843776917740045787889/395271457031250:ℝ), (527797635005660997114161/395271457031250:ℝ), (261040109850231809513648/197635728515625:ℝ), (86063180806271333850512/197635728515625:ℝ)],
![(229450850856339305067103/263514304687500:ℝ), (2042199689757426923522077/790542914062500:ℝ), (33656800880600386296736/13175715234375:ℝ), (166390228911903542370848/197635728515625:ℝ)],
![(532548673852395355786853/1264868662500000:ℝ), (2632375590379122532819283/2108114437500000:ℝ), (243946676980245567178576/197635728515625:ℝ), (26790731890546534689488/65878576171875:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1674420743159158418093/7859620282368000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ]
 ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
#print axioms row008_identity
#print axioms row008_pos
end
end LewkoStage2Return.C30
