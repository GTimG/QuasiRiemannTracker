/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![![(427268934038942732835992697119/3333056606486271010546875000:ℝ),(380025817395832570475508244091/1111018868828757003515625000:ℝ),(2019643312709644192398776419103/6666113212972542021093750000:ℝ),(13185315646707470361018607751/148135849177167600468750000:ℝ)],
![(273880719520697932696109035691/1666528303243135505273437500:ℝ),(112671472402768247580694826947/277754717207189250878906250:ℝ),(182845030316614816924444216297/555509434414378501757812500:ℝ),(1456999037432348290133977229/16665283032431355052734375:ℝ)],
![(227150316410013804893725374263/3333056606486271010546875000:ℝ),(173111733943937934818620627547/1111018868828757003515625000:ℝ),(383803560761843818386567627443/3333056606486271010546875000:ℝ),(18048906143729536176136223813/666611321297254202109375000:ℝ)]]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (18048906143729536176136223813/303382219114839245760000000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ]
 ring
theorem row037_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
#print axioms row037_identity
#print axioms row037_pos
end
end LewkoStage2Finite
