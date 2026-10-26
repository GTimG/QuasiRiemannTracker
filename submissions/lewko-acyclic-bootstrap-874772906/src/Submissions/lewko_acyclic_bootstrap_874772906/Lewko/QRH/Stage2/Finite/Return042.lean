/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15650432878444241145165196507927/296451224472656250000000:ℝ),(15494790566699201991540239519671/98817074824218750000000:ℝ),(15339794816055047855662398578479/98817074824218750000000:ℝ),(15185445626511778737531673684351/296451224472656250000000:ℝ)],
![(14759145156608181268219165844647/148225612236328125000000:ℝ),(4867819472942158002987795838813/16469512470703125000000:ℝ),(43345333515022169385495234110849/148225612236328125000000:ℝ),(1588233712794547625202693045131/16469512470703125000000:ℝ)],
![(13905142002190933948003056396607/296451224472656250000000:ℝ),(13749421049060026350397306298663/98817074824218750000000:ℝ),(8156640063174165088130859275123/59290244894531250000000:ℝ),(13440079170881680337465433876233/296451224472656250000000:ℝ)]]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (13440079170881680337465433876233/141472034885468160000000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ]
 ring
theorem row042_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
#print axioms row042_identity
#print axioms row042_pos
end
end LewkoStage2Finite
