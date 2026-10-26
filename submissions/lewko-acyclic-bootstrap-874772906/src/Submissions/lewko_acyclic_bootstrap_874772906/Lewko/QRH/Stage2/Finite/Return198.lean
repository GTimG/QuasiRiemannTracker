/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(41194308029289736988983049428/3595179924718927734375:ℝ),(21533904174437935298508882244/719035984943785546875:ℝ),(92005224109066755568038740662/3595179924718927734375:ℝ),(1702000751077787737631825258/239678661647928515625:ℝ)],
![(78607514053065311596835145656/3595179924718927734375:ℝ),(202929867691514269827260847304/3595179924718927734375:ℝ),(170545597547319604404605151488/3595179924718927734375:ℝ),(3081549593924709744945296656/239678661647928515625:ℝ)],
![(39355663899950519699622742348/3595179924718927734375:ℝ),(101064042721508196302997322052/3595179924718927734375:ℝ),(84320485095488406471343898956/3595179924718927734375:ℝ),(7537368757976909955989773084/1198393308239642578125:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1884342189494227488997443271/4575164503675121958912000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
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
end LewkoStage2Finite
