/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row012_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30744537239350152812754255770943726299/12442745794525649338206234375:ℝ),(11417793575625477940718815269185789790637/1555343224315706167275779296875:ℝ),(1256313067288549743681079093205526151277/172815913812856240808419921875:ℝ),(15358397976315997254292099088608688717/6400589400476157066978515625:ℝ)],
![(1484043956660660052339859910128961802662/311068644863141233455155859375:ℝ),(22040044112144091159382237668282563176474/1555343224315706167275779296875:ℝ),(2424477584031387103059568528102756701458/172815913812856240808419921875:ℝ),(3292397324674982750702347701320098834/711176600052906340775390625:ℝ)],
![(238626015508953255765813358688624694841/103689548287713744485051953125:ℝ),(3542988301242063232661083127613883515263/518447741438568722425259765625:ℝ),(129878968137348964464872663878564547879/19201768201428471200935546875:ℝ),(21159099198117568355548959189309241/9482354667372084543671875:ℝ)]]
theorem row012_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (190431892783058115199940632703783169/1303244901933953964109369180160000000:ℝ) row012_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row012_coefficients,Fin.sum_univ_succ]
 ring
theorem row012_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row012_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_coefficients]
#print axioms row012_identity
#print axioms row012_pos
end
end LewkoStage2Finite
