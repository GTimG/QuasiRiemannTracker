/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row185_coefficients : Fin 3 → Fin 4 → ℝ := ![![(123738630029321362825694816/56826619691052734375:ℝ), (25268271011873983135887881312/4602956194975271484375:ℝ), (20620634447100734239991489536/4602956194975271484375:ℝ), (1075038493520356298596977664/920591238995054296875:ℝ)],
![(2078448147084980263085524208/511439577219474609375:ℝ), (46192593367584442675785194608/4602956194975271484375:ℝ), (4765947970264941624424448/599733706185703125:ℝ), (9092090627963806659442161664/4602956194975271484375:ℝ)],
![(999378883626068082870540614/511439577219474609375:ℝ), (21850381976663746866906800246/4602956194975271484375:ℝ), (16876578664714249985774174464/4602956194975271484375:ℝ), (4020606640685115864702239744/4602956194975271484375:ℝ)]]
theorem row185_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3926373672544058461623281/8580532257959804928000000000:ℝ) row185_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row185_coefficients,Fin.sum_univ_succ]
 ring
theorem row185_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row185_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row185_coefficients]
#print axioms row185_identity
#print axioms row185_pos
end
end LewkoStage2Return.C30
