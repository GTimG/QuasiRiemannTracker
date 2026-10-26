/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row178_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1466996290996861335618261529243/414018492151783883592234375000:ℝ), (3932292436673297161651519156819/414018492151783883592234375000:ℝ), (3463596000356010316448253725909/414018492151783883592234375000:ℝ), (998299854679574490414996098333/414018492151783883592234375000:ℝ)],
![(485318096517741056021804170667/414018492151783883592234375000:ℝ), (2459811429538424585322516871543/828036984303567767184468750000:ℝ), (272631737285827478058628955323/103504623037945970898058593750:ℝ), (5535029294269418809520984899/6624295874428542137475750000:ℝ)],
![(1590556071056639751821887126/976458707905150668849609375:ℝ), (368205741484546017328874037811/165607396860713553436893750000:ℝ), (646653040637777426629847018641/828036984303567767184468750000:ℝ), (21385335555797904971531056217/414018492151783883592234375000:ℝ)]]
theorem row178_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21385335555797904971531056217/23553051997968149822136000000000:ℝ) row178_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row178_coefficients,Fin.sum_univ_succ]
 ring
theorem row178_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row178_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row178_coefficients]
#print axioms row178_identity
#print axioms row178_pos
end
end LewkoStage1Return.C30
