/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1727757361085375866195512481/26664878889575648437500:ℝ), (1652894474792727399583874977/8888292963191882812500:ℝ), (4739179762213219274754266819/26664878889575648437500:ℝ), (167578857345527191410906041/2962764321063960937500:ℝ)],
![(1429707118707118662666232513/13332439444787824218750:ℝ), (1357193156977611872620603361/4444146481595941406250:ℝ), (428863929524788695610192403/1481382160531980468750:ℝ), (1217848034984046030921154057/13332439444787824218750:ℝ)],
![(235619647936619657797587509/5332975777915129687500:ℝ), (73835303558569641179047303/592552864212792187500:ℝ), (623456348760979050514257677/5332975777915129687500:ℝ), (194544520042138119106669459/5332975777915129687500:ℝ)]]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (194544520042138119106669459/2485346848579171123200000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ]
 ring
theorem row039_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
#print axioms row039_identity
#print axioms row039_pos
end
end LewkoStage2Return.C30
