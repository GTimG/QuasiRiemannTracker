/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2273401910481117827188823667617039/1666528303243135505273437500:ℝ),(6621128191363967338288992078287117/1666528303243135505273437500:ℝ),(2141715414198225232267440414616039/555509434414378501757812500:ℝ),(25646947961778502888615505656519/20574423496828833398437500:ℝ)],
![(676155773956687467621961102567669/277754717207189250878906250:ℝ),(1963291578235013889601485727702543/277754717207189250878906250:ℝ),(633066463706725909563895929262193/92584905735729750292968750:ℝ),(40803819245266882738661398343447/18516981147145950058593750:ℝ)],
![(72245537578988444839276237839823/66661132129725420210937500:ℝ),(5226137278589942028695848849162141/1666528303243135505273437500:ℝ),(1679088348767979290939819898614669/555509434414378501757812500:ℝ),(179693935916812038724346397103049/185169811471459500585937500:ℝ)]]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (179693935916812038724346397103049/2761452376654181223628800000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row062_coefficients,Fin.sum_univ_succ]
 ring
theorem row062_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row062_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_coefficients]
#print axioms row062_identity
#print axioms row062_pos
end
end LewkoStage2Finite
