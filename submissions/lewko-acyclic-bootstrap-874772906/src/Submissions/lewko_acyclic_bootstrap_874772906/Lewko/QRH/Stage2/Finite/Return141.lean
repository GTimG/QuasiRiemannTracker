/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row141_coefficients : Fin 3 → Fin 4 → ℝ := ![![(260343627941396156895524997542229583/76035637088287601984329500000000000:ℝ),(698328024779940740144903615624359789/76035637088287601984329500000000000:ℝ),(615625165735693009603232238622030829/76035637088287601984329500000000000:ℝ),(177640768897148426353853620539900623/76035637088287601984329500000000000:ℝ)],
![(37984159125833510923147161750287551/38017818544143800992164750000000000:ℝ),(96645224174994222437005590781946677/38017818544143800992164750000000000:ℝ),(87067549390691643305802480586541201/38017818544143800992164750000000000:ℝ),(1136259373661237271677762062195283/1520712741765752039686590000000000:ℝ)],
![(119767238663421272888087325958345519/76035637088287601984329500000000000:ℝ),(31885970689679118361375119979050953/15207127417657520396865900000000000:ℝ),(52208631805463864222595355908653423/76035637088287601984329500000000000:ℝ),(2284682022673877750814944471744177/76035637088287601984329500000000000:ℝ)]]
theorem row141_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2284682022673877750814944471744177/4325582909911472468441856000000000000:ℝ) row141_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row141_coefficients,Fin.sum_univ_succ]
 ring
theorem row141_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row141_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row141_coefficients]
#print axioms row141_identity
#print axioms row141_pos
end
end LewkoStage2Finite
