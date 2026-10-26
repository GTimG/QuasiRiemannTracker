/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74575202493560658016519933/632429278875000000:ℝ),(73806152178010026166651357/210809759625000000:ℝ),(73039272758445338260462597/210809759625000000:ℝ),(72274564234866594297953653/632429278875000000:ℝ)],
![(559640192712099101539697/2529717115500000:ℝ),(23063643825586762088357887/35134959937500000:ℝ),(41057454229714863585959503/63242927887500000:ℝ),(7518833423033982980782073/35134959937500000:ℝ)],
![(65475063454104162271689397/632429278875000000:ℝ),(64716633210800698303183277/210809759625000000:ℝ),(191881612097865964998001333/632429278875000000:ℝ),(63206775919568032360140899/632429278875000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (63206775919568032360140899/301807007755665408000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
#print axioms row007_identity
#print axioms row007_pos
end
end LewkoStage2Finite
