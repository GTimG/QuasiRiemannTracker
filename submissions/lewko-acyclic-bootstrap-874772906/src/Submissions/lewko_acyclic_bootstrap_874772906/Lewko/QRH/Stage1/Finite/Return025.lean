/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row025_coefficients : Fin 3 → Fin 4 → ℝ := ![![(66409000135816924171663287167329942828426/1866415745721910063787947265625:ℝ),(197178905105793807355555891263392439114634/1866415745721910063787947265625:ℝ),(1561113998988561826898193058053683812864/14931325965775280510303578125:ℝ),(64369334889682568517341004441897980321792/1866415745721910063787947265625:ℝ)],
![(131589811508761395136717822254584971607936/1866415745721910063787947265625:ℝ),(390683880333220462291541006195962930020224/1866415745721910063787947265625:ℝ),(77323045987349820095655325417094222839808/373283149144382012757589453125:ℝ),(127521140958507338156579433144093155786752/1866415745721910063787947265625:ℝ)],
![(13036699637223090610150964752939480598528/373283149144382012757589453125:ℝ),(38702607432682017412221235756892019574784/373283149144382012757589453125:ℝ),(38296808662114643423992809601286402473984/373283149144382012757589453125:ℝ),(12630898838602112076828298597333863497728/373283149144382012757589453125:ℝ)]]
theorem row025_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3011440953875091571051668786366907/21745319522067750744961228800000000:ℝ) row025_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row025_coefficients,Fin.sum_univ_succ]
 ring
theorem row025_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row025_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_coefficients]
#print axioms row025_identity
#print axioms row025_pos
end
end LewkoStage1Finite
