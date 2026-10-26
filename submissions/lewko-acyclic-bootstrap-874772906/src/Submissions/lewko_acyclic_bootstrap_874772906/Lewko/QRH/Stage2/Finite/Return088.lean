/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row088_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2814074619644494285395764347035194949584/600080871373666668502435546875:ℝ),(74424388667089318289859312831167511148112/5400727842363000016521919921875:ℝ),(14576387071543242682509487391402255015936/1080145568472600003304383984375:ℝ),(1829553350725954990230662191281578344448/415440603258692308963224609375:ℝ)],
![(428708231574609212105977225514386849136/46160067028743589884802734375:ℝ),(29469838155231853060337339713792775426672/1080145568472600003304383984375:ℝ),(144248296097206128949017838941341518045184/5400727842363000016521919921875:ℝ),(47057918678413297738678966820060902260736/5400727842363000016521919921875:ℝ)],
![(184068909655192067827856569828519461644/40005391424911111233495703125:ℝ),(14595198159612668660581512520980258252868/1080145568472600003304383984375:ℝ),(1098729303569584139790978707666977839104/83088120651738461792644921875:ℝ),(4658138341499162431311140735935479119872/1080145568472600003304383984375:ℝ)]]
theorem row088_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (142155100753758619119602683591780979/64433192937627023420580849254400000000:ℝ) row088_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row088_coefficients,Fin.sum_univ_succ]
 ring
theorem row088_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row088_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_coefficients]
#print axioms row088_identity
#print axioms row088_pos
end
end LewkoStage2Finite
