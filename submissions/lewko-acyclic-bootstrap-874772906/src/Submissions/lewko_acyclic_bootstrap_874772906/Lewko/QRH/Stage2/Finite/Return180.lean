/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row180_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3870453266220652890977131414361281207/1900890927207190049608237500000000:ℝ),(8441965233303277042818051167968076221/1900890927207190049608237500000000:ℝ),(5604924696877444186696611647396190071/1900890927207190049608237500000000:ℝ),(1026999395421185242635071807851895057/1900890927207190049608237500000000:ℝ)],
![(26421608664248358299906156058051839771/4752227318017975124020593750000000:ℝ),(59901972641116222476550487888522816801/4752227318017975124020593750000000:ℝ),(42502325149411647772528997793059359789/4752227318017975124020593750000000:ℝ),(8983481166301974842560945446963382759/4752227318017975124020593750000000:ℝ)],
![(43555821144612140393086353317733631307/9504454636035950248041187500000000:ℝ),(106592817622203134720098619958264008897/9504454636035950248041187500000000:ℝ),(84836916866071603614148050827017368073/9504454636035950248041187500000000:ℝ),(21753744380990438783147319567736990483/9504454636035950248041187500000000:ℝ)]]
theorem row180_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1026999395421185242635071807851895057/885879379949869561536892108800000000000:ℝ) row180_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row180_coefficients,Fin.sum_univ_succ]
 ring
theorem row180_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row180_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row180_coefficients]
#print axioms row180_identity
#print axioms row180_pos
end
end LewkoStage2Finite
