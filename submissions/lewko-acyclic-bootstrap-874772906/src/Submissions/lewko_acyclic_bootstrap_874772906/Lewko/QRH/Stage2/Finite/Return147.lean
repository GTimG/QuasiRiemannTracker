/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row147_coefficients : Fin 3 → Fin 4 → ℝ := ![![(392106514666192960303197977916250301/845352343945940625000000000000:ℝ),(946546794966744174927072561975788711/845352343945940625000000000000:ℝ),(723805306931069091507904962803667067/845352343945940625000000000000:ℝ),(169365026630517876884030378744128657/845352343945940625000000000000:ℝ)],
![(357623741974294133214722784158486981/422676171972970312500000000000:ℝ),(827501607582171965910840305993199287/422676171972970312500000000000:ℝ),(117891514579737065229775785346940609/84535234394594062500000000000:ℝ),(119579707290807493452761404899990739/422676171972970312500000000000:ℝ)],
![(381515598715483056838847011975588721/845352343945940625000000000000:ℝ),(176432552316498833282882118976511491/169070468789188125000000000000:ℝ),(156852408607973873395233686972050231/211338085986485156250000000000:ℝ),(12676247156488438400537116498123219/84535234394594062500000000000:ℝ)]]
theorem row147_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (119579707290807493452761404899990739/403417852316084286259200000000000000000:ℝ) row147_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row147_coefficients,Fin.sum_univ_succ]
 ring
theorem row147_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row147_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row147_coefficients]
#print axioms row147_identity
#print axioms row147_pos
end
end LewkoStage2Finite
