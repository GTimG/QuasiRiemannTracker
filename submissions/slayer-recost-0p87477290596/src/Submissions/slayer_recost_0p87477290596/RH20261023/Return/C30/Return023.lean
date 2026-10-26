/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row023_coefficients : Fin 3 → Fin 4 → ℝ := ![![(238693008288740568676976316393519121024/210735008282660885736328125:ℝ), (2137160819696682734668034303827472115584/632205024847982657208984375:ℝ), (708702361185466012498757782318774288384/210735008282660885736328125:ℝ), (141005055108462922679864268461881622528/126441004969596531441796875:ℝ)],
![(1425466887595728129927033514924316671808/632205024847982657208984375:ℝ), (4254276730470457886627388467819305717568/632205024847982657208984375:ℝ), (4232197867964354719288116956697225920512/632205024847982657208984375:ℝ), (1403387998638939523595538028802236874752/632205024847982657208984375:ℝ)],
![(709395175977660804801651458857290842936/632205024847982657208984375:ℝ), (705712617603341026547578410139495655528/210735008282660885736328125:ℝ), (421222545722530362342004652500769349632/126441004969596531441796875:ℝ), (77596670945899385221630583368627847168/70245002760886961912109375:ℝ)]]
theorem row023_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1184031233915701068445290883920713/8380555265706644704591872000000000:ℝ) row023_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row023_coefficients,Fin.sum_univ_succ]
 ring
theorem row023_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row023_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_coefficients]
#print axioms row023_identity
#print axioms row023_pos
end
end RH20261023Return.C30
