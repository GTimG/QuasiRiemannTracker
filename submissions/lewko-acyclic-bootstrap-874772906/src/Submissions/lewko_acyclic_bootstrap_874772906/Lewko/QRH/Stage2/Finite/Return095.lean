/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row095_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3239412366049815834813646336488013575482/5400727842363000016521919921875:ℝ),(1860246492605359729816254149818671616882/1080145568472600003304383984375:ℝ),(8891255419450420815067937028303815804416/5400727842363000016521919921875:ℝ),(2829408984022881817033509150073471295488/5400727842363000016521919921875:ℝ)],
![(6440624013175554914909131550722216264576/5400727842363000016521919921875:ℝ),(18483381480235434640908110944315946959744/5400727842363000016521919921875:ℝ),(3531805624780048139587289821485884243968/1080145568472600003304383984375:ℝ),(5616217648637983746746418713835690524672/5400727842363000016521919921875:ℝ)],
![(640673752643882613920992556177312647168/1080145568472600003304383984375:ℝ),(1837716767226756169294715225323454531584/1080145568472600003304383984375:ℝ),(1754834246377621957255212215555511025664/1080145568472600003304383984375:ℝ),(557785897636018618214465546409369141248/1080145568472600003304383984375:ℝ)]]
theorem row095_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (132986521157269148400894533731787/62923039978151390059160985600000000:ℝ) row095_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row095_coefficients,Fin.sum_univ_succ]
 ring
theorem row095_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row095_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row095_coefficients]
#print axioms row095_identity
#print axioms row095_pos
end
end LewkoStage2Finite
