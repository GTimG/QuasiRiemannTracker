/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![![(792347359180262360792173917307/26664452851890168084375000000:ℝ),(694627458824520822035843854027/8888150950630056028125000000:ℝ),(596907558468779283279513790747/8888150950630056028125000000:ℝ),(499187658113037744523183727467/26664452851890168084375000000:ℝ)],
![(532301333254456888314790255879/13332226425945084042187500000:ℝ),(440404416112339113942291207361/4444075475315028014062500000:ℝ),(1064832606969025881970623837029/13332226425945084042187500000:ℝ),(1226314186162068570926846537/59254339670867040187500000:ℝ)],
![(378913118736212088174906594451/26664452851890168084375000000:ℝ),(56885377089998352690787537679/1777630190126011205625000000:ℝ),(615716172877933803616173692467/26664452851890168084375000000:ℝ),(138600346021378325541767221733/26664452851890168084375000000:ℝ)]]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (138600346021378325541767221733/1516911095574196228800000000000:ℝ) row036_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ]
 ring
theorem row036_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
#print axioms row036_identity
#print axioms row036_pos
end
end LewkoStage2Finite
