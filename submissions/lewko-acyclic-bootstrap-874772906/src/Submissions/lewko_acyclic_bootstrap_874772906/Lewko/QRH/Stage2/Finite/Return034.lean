/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7655438783393078512493495229179/22220377376575140070312500:ℝ),(21592799141335749299792269811659/22220377376575140070312500:ℝ),(5065432514560001871865939876456/5555094344143785017578125:ℝ),(1580992573793804281211582168336/5555094344143785017578125:ℝ)],
![(670155319062607682517313192822/1111018868828757003515625:ℝ),(9390443669433657903383010894094/5555094344143785017578125:ℝ),(8750289111133074090139473065056/5555094344143785017578125:ℝ),(2710404179673116649169215635072/5555094344143785017578125:ℝ)],
![(484457263888662583842369652292/1851698114714595005859375:ℝ),(1347361155247971753959131345028/1851698114714595005859375:ℝ),(1245043172152612796271666928256/1851698114714595005859375:ℝ),(76419934073593890679206047104/370339622942919001171875:ℝ)]]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (597030734949952270931297243/5393461673152697702400000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ]
 ring
theorem row034_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
#print axioms row034_identity
#print axioms row034_pos
end
end LewkoStage2Finite
