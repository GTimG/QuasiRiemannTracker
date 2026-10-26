/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row067_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4901557444641345476361859957127635125122/4851243019246921616226884765625:ℝ),(14558916710716344547212627350463750256514/4851243019246921616226884765625:ℝ),(1601536749256745163662703744169109344768/539027002138546846247431640625:ℝ),(105699340494829560408259183495797088256/107805400427709369249486328125:ℝ)],
![(9482677548758961766062491495638623281512/4851243019246921616226884765625:ℝ),(5631710114001953023216136723626152218696/970248603849384323245376953125:ℝ),(27870422305402742264524513333536399591424/4851243019246921616226884765625:ℝ),(9194546917875263708791202773544261779456/4851243019246921616226884765625:ℝ)],
![(916986523279263603171975513141911733928/970248603849384323245376953125:ℝ),(13611051078210239741933229831994233254216/4851243019246921616226884765625:ℝ),(13467988418381950591883656474810030016512/4851243019246921616226884765625:ℝ),(4441868744572658638492804521025355431936/4851243019246921616226884765625:ℝ)]]
theorem row067_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (271110152866983559478320588441488979/4521686222355431182805975040000000000:ℝ) row067_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row067_coefficients,Fin.sum_univ_succ]
 ring
theorem row067_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row067_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_coefficients]
#print axioms row067_identity
#print axioms row067_pos
end
end LewkoStage1Finite
