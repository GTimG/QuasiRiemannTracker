/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row189_coefficients : Fin 3 → Fin 4 → ℝ := ![![(865677095548461207710128396231821749/20698636882120198895901375000000000:ℝ),(12990235933731299469735550141327002821/186287731939081790063112375000000000:ℝ),(2893527075364458578538939081022616747/93143865969540895031556187500000000:ℝ),(180824558252971972304034077464813207/93143865969540895031556187500000000:ℝ)],
![(223795576719722820223173928544168639/1724886406843349907991781250000000:ℝ),(11029109787395421569321907394232467807/46571932984770447515778093750000000:ℝ),(1202562411142148530634934727213377031/9314386596954089503155618750000000:ℝ),(875340866129287488461518691276970601/46571932984770447515778093750000000:ℝ)],
![(1125728838152791923180553110008019497/10349318441060099447950687500000000:ℝ),(20515058455563333471340622250526801891/93143865969540895031556187500000000:ℝ),(13360983812181349934178396398737888763/93143865969540895031556187500000000:ℝ),(555272453700348823248032128656652469/18628773193908179006311237500000000:ℝ)]]
theorem row189_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (180824558252971972304034077464813207/169563233338328669355224064000000000000:ℝ) row189_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row189_coefficients,Fin.sum_univ_succ]
 ring
theorem row189_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row189_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row189_coefficients]
#print axioms row189_identity
#print axioms row189_pos
end
end LewkoStage1Finite
