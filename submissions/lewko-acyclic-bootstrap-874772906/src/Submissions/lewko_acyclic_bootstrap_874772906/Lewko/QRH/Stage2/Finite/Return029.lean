/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3574940965667414487840955378587382164527/1555343224315706167275779296875:ℝ),(10617822306696206104976750425561923760781/1555343224315706167275779296875:ℝ),(1167918234443021779529514932358854043109/172815913812856240808419921875:ℝ),(14273177945758847502029030223272200789/6400589400476157066978515625:ℝ)],
![(765879757977740193302375285477083394926/172815913812856240808419921875:ℝ),(151607104023080395593906784563069183382/11521060920857082720561328125:ℝ),(750224234771181485992632788816271336014/57605304604285413602806640625:ℝ),(3055332434760287755962340055472673466/711176600052906340775390625:ℝ)],
![(3320214460382014928262604991758895586487/1555343224315706167275779296875:ℝ),(9855851103627223779520492474197293155741/1555343224315706167275779296875:ℝ),(1083500666363825999253747974099810345663/172815913812856240808419921875:ℝ),(13234027980054253439598547505493397291/6400589400476157066978515625:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (13234027980054253439598547505493397291/97743367645046547308202688512000000000:ℝ) row029_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
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
end LewkoStage2Finite
