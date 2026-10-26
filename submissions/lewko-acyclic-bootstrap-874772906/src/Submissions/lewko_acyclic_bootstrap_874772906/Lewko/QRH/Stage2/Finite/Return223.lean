/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row223_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18214469662426504385981543296499749/2694752055959547560431429687500:ℝ),(109621507853183285203512673240285183/8084256167878642681294289062500:ℝ),(15411321402634889456106020550137312/2021064041969660670323572265625:ℝ),(1633824389570592046205900204628328/2021064041969660670323572265625:ℝ)],
![(11397672831733596186788091752331458/673688013989886890107857421875:ℝ),(72479346721267509171939689827082726/2021064041969660670323572265625:ℝ),(45807049405664619062395151795047408/2021064041969660670323572265625:ℝ),(7448781623405125217711134662459056/2021064041969660670323572265625:ℝ)],
![(7477730325464985764742478214749756/673688013989886890107857421875:ℝ),(10109054934937563843689721379389524/404212808393932134064714453125:ℝ),(35645922073547829336561690112230344/2021064041969660670323572265625:ℝ),(7494598617331636557917643734531992/2021064041969660670323572265625:ℝ)]]
theorem row223_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (204228048696324005775737525578541/470942055304973090454491136000000000:ℝ) row223_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row223_coefficients,Fin.sum_univ_succ]
 ring
theorem row223_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row223_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row223_coefficients]
#print axioms row223_identity
#print axioms row223_pos
end
end LewkoStage2Finite
