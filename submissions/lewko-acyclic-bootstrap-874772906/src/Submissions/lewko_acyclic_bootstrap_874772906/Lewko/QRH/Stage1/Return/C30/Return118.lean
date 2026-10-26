/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row118_coefficients : Fin 3 → Fin 4 → ℝ := ![![(47702360537570835705523782415162719092/37318998047758674969568359375:ℝ), (140406889768725604576290363073264807004/37318998047758674969568359375:ℝ), (137729054062752976461310959669578733532/37318998047758674969568359375:ℝ), (9004896782405235325724505802295329124/7463799609551734993913671875:ℝ)],
![(18690620629760276446919283806774080712/7463799609551734993913671875:ℝ), (274903876655902385556694699996434578104/37318998047758674969568359375:ℝ), (269493697830829497934653324390299796728/37318998047758674969568359375:ℝ), (88042841407753589768660768427735622184/37318998047758674969568359375:ℝ)],
![(45870955445632240427722291769336730068/37318998047758674969568359375:ℝ), (5394264710068867542862811775057902972/1492759921910346998782734375:ℝ), (132123270250930855098373669427526128596/37318998047758674969568359375:ℝ), (43137565941354119632289751195415284364/37318998047758674969568359375:ℝ)]]
theorem row118_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (10784391485338529908072437798853821091/4559185810051167433801668231168000000000:ℝ) row118_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row118_coefficients,Fin.sum_univ_succ]
 ring
theorem row118_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row118_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row118_coefficients]
#print axioms row118_identity
#print axioms row118_pos
end
end LewkoStage1Return.C30
