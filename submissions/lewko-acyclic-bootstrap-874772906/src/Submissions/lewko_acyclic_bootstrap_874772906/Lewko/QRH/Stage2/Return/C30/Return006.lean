/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7657757782250782691481493754/2222073240797970703125:ℝ), (22347495849615910133095157146/2222073240797970703125:ℝ), (4345852297158089233874358811/444414648159594140625:ℝ), (2346498894363695542448022721/740691080265990234375:ℝ)],
![(4526288767059071862994470548/740691080265990234375:ℝ), (39521802044880951420519585316/2222073240797970703125:ℝ), (1532905211902443494140528168/88882929631918828125:ℝ), (4126545047334500803315260176/740691080265990234375:ℝ)],
![(1194752917724309921817830798/444414648159594140625:ℝ), (1155535615731166639861679198/148138216053198046875:ℝ), (3350564686124384684545195294/444414648159594140625:ℝ), (359568051779366780332246166/148138216053198046875:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (179784025889683390166123083/1104598599368520499200000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ]
 ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
#print axioms row006_identity
#print axioms row006_pos
end
end LewkoStage2Return.C30
