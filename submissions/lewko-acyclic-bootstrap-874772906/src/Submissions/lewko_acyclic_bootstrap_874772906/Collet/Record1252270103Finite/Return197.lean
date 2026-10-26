/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9085843770420741421564370231932/4793607781307088134765625:ℝ), (22301192297460808081677489473404/4793607781307088134765625:ℝ), (17503728144022340793925780406912/4793607781307088134765625:ℝ), (857675923396454826762532233088/958721556261417626953125:ℝ)],
![(5631192973891174739221449529058/1597869260435696044921875:ℝ), (40428548929697188269579246808486/4793607781307088134765625:ℝ), (406677077493766617313399890944/63914770417427841796875:ℝ), (6965810804008832246590093599488/4793607781307088134765625:ℝ)],
![(32524413840239993205445889872343/19174431125228352539062500:ℝ), (25452757550979978742459541187101/6391477041742784179687500:ℝ), (13951433492651471092027715997088/4793607781307088134765625:ℝ), (997656263158828445514844191616/1597869260435696044921875:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (7794189555928347230584720247/23829153530746601472000000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ]
 ring
theorem row197_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
#print axioms row197_identity
#print axioms row197_pos
end
end Record1252270103Finite
