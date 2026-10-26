/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1318311414381862172129251132556/115045786711731287109375:ℝ),(689140789364269318298712581276/23009157342346257421875:ℝ),(2944445058404278097049141776282/115045786711731287109375:ℝ),(272350841988264559228276667486/38348595570577095703125:ℝ)],
![(2515622423389396943067973372552/115045786711731287109375:ℝ),(6494298904945745803043659527416/115045786711731287109375:ℝ),(5457999480979854783381454333696/115045786711731287109375:ℝ),(493107666474501974468589392944/38348595570577095703125:ℝ)],
![(1259469700906686449610098803796/115045786711731287109375:ℝ),(3234313346755712022863016371356/115045786711731287109375:ℝ),(2698518115545754315279081057364/115045786711731287109375:ℝ),(241224823232242914008721163268/38348595570577095703125:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (60306205808060728502180290817/146405301176141409681408000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row198_coefficients,Fin.sum_univ_succ]
 ring
theorem row198_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row198_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]
#print axioms row198_identity
#print axioms row198_pos
end
end LewkoStage1Finite
