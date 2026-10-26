/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1460760290109837651422681127566027458/632205024847982657208984375:ℝ), (53567021309326929182101212237694054/7805000306765217990234375:ℝ), (4295754453755550344772918182844354374/632205024847982657208984375:ℝ), (157509534063084412597822346573018162/70245002760886961912109375:ℝ)],
![(2816549336002972735698664056813574276/632205024847982657208984375:ℝ), (8363831398740153166881432733780127372/632205024847982657208984375:ℝ), (8278372537232029089845315297398755916/632205024847982657208984375:ℝ), (60690889809965494879539924898493396/14049000552177392382421875:ℝ)],
![(452234068061315555125171267350821606/210735008282660885736328125:ℝ), (4027642904618499178290944588359004198/632205024847982657208984375:ℝ), (3985359011397025724613444525419621042/632205024847982657208984375:ℝ), (146046454336243611088094234901453518/70245002760886961912109375:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (73023227168121805544047117450726759/536355537005225261093879808000000000:ℝ) row029_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row029_coefficients,Fin.sum_univ_succ]
 ring
theorem row029_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row029_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_coefficients]
#print axioms row029_identity
#print axioms row029_pos
end
end RH20261023Return.C30
