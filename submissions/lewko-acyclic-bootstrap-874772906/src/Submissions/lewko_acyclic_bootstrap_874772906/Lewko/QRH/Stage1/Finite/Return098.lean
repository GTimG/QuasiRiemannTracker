/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row098_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5826070697712745221825515854056275042/3818270884159084451369101171875:ℝ),(16184991526905860040113902466516244326/3818270884159084451369101171875:ℝ),(14932250116120194040483698407809653526/3818270884159084451369101171875:ℝ),(4573045909775941446549061795349684242/3818270884159084451369101171875:ℝ)],
![(57216207794676307560380858183637540788/19091354420795422256845505859375:ℝ),(158148328000707161200785266133386811836/19091354420795422256845505859375:ℝ),(145071537215465063446110461717882537908/19091354420795422256845505859375:ℝ),(8827288309869452632284085753626653372/3818270884159084451369101171875:ℝ)],
![(29102223486133021890698686576200778678/19091354420795422256845505859375:ℝ),(80239023353761748815906302799955291926/19091354420795422256845505859375:ℝ),(73392914732708092059833093857266091373/19091354420795422256845505859375:ℝ),(1424291375906157961368033568544741/1221846682930907024438112375:ℝ)]]
theorem row098_identity (δ p : ℝ) : rowMargin .oldSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (2206822077467363158071021438406663343/911074920818459565551799553228800000000:ℝ) row098_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row098_coefficients,Fin.sum_univ_succ]
 ring
theorem row098_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .P δ p := by
 rw [row098_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row098_coefficients]
#print axioms row098_identity
#print axioms row098_pos
end
end LewkoStage1Finite
