/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row132_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2634661498677811469494245842531/38578690828283447003906250:ℝ),(6943459220486616821908597558393/38578690828283447003906250:ℝ),(6035052192927048382468021436693/38578690828283447003906250:ℝ),(575244519059929197940285740277/12859563609427815667968750:ℝ)],
![(533603650128930913340331252703/3857869082828344700390625:ℝ),(6954743345304065646665676532009/19289345414141723501953125:ℝ),(5962121911706847606772370462603/19289345414141723501953125:ℝ),(558274603905045182317418814703/6429781804713907833984375:ℝ)],
![(3000386944101788753747663108543/38578690828283447003906250:ℝ),(46424842996386399946103029993/228276277090434597656250:ℝ),(3376045480540280741154696086308/19289345414141723501953125:ℝ),(317674855487919594553990014557/6429781804713907833984375:ℝ)]]
theorem row132_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (558274603905045182317418814703/191775712303208977661952000000000:ℝ) row132_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row132_coefficients,Fin.sum_univ_succ]
 ring
theorem row132_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row132_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row132_coefficients]
#print axioms row132_identity
#print axioms row132_pos
end
end LewkoStage2Finite
