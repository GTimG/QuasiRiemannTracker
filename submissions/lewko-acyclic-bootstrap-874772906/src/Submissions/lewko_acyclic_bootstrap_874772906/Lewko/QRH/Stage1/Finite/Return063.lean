/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row063_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13828500822901746652554911968339137391/388099441539753729298150781250:ℝ),(40726675173579306497806740504464157133/388099441539753729298150781250:ℝ),(13324832642411799954943244406231303631/129366480513251243099383593750:ℝ),(4358767196749089667493468227522963717/129366480513251243099383593750:ℝ)],
![(324828833464753802371231332775699339639/4851243019246921616226884765625:ℝ),(50303337692186959960465205760020208967/255328579960364295590888671875:ℝ),(49326860745747227185109146163884044991/255328579960364295590888671875:ℝ),(61255038868349278088131365089822444819/970248603849384323245376953125:ℝ)],
![(304913416911699933611196296408162489503/9702486038493843232453769531250:ℝ),(896254730515567128733604954807502486421/9702486038493843232453769531250:ℝ),(877942965073223756997202694253077383583/9702486038493843232453769531250:ℝ),(3016853110228120507537307285302498807/102131431984145718236355468750:ℝ)]]
theorem row063_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (3016853110228120507537307285302498807/48739017807283805591508615168000000000:ℝ) row063_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row063_coefficients,Fin.sum_univ_succ]
 ring
theorem row063_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row063_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_coefficients]
#print axioms row063_identity
#print axioms row063_pos
end
end LewkoStage1Finite
