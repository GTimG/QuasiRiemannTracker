/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(163846884612787976754370999/47432196421875000:ℝ),(5145334416285442958593033/499286278125000:ℝ),(972153878009079619807704569/94864392843750000:ℝ),(107411369380140470394590099/31621464281250000:ℝ)],
![(6336248460661788236463733/948643928437500:ℝ),(472494602627559117996740291/23716098210937500:ℝ),(117443674507564975147295272/5929024552734375:ℝ),(25947717819874248084005687/3952683035156250:ℝ)],
![(8055312712840148171333371/2496431390625000:ℝ),(24023120175894330199439753/2496431390625000:ℝ),(23880523366787520380354299/2496431390625000:ℝ),(2637571967911112784082639/832143796875000:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2637571967911112784082639/12707663620079616000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ]
 ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
#print axioms row009_identity
#print axioms row009_pos
end
end LewkoStage1Finite
