/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row021_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14354170971037722681539265584907281469832/1555343224315706167275779296875:ℝ),(113677819168711768939269520081024826552/4147581931508549779402078125:ℝ),(520957958975038250280949024894085552128/19201768201428471200935546875:ℝ),(556903258060013726380447664337756049408/62213728972628246691031171875:ℝ)],
![(28189881027832007409582134448346243659848/1555343224315706167275779296875:ℝ),(27902469909045700783975750047051137116184/518447741438568722425259765625:ℝ),(82848673117907131050539465206802332370944/1555343224315706167275779296875:ℝ),(1822076023374090285910134203433010978816/103689548287713744485051953125:ℝ)],
![(13837949061946118934568732550210265653314/1555343224315706167275779296875:ℝ),(2738996386756097623440538758087217916318/103689548287713744485051953125:ℝ),(40657797796199700186419661975027307661824/1555343224315706167275779296875:ℝ),(13410798996732150514612078663304304570368/1555343224315706167275779296875:ℝ)]]
theorem row021_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3274120848811560184231464517408277483/23194959314205381831927005184000000000:ℝ) row021_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row021_coefficients,Fin.sum_univ_succ]
 ring
theorem row021_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row021_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_coefficients]
#print axioms row021_identity
#print axioms row021_pos
end
end LewkoStage2Finite
