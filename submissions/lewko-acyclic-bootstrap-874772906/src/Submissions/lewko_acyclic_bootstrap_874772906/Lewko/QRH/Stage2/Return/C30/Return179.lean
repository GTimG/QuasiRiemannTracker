/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row179_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9021793086780560399750810911031/828036984303567767184468750000:ℝ), (18243995510960235431290390095137/828036984303567767184468750000:ℝ), (11444552302699607227280322435331/828036984303567767184468750000:ℝ), (84428186726418006246134730049/33121479372142710687378750000:ℝ)],
![(15929580700686876027936059808479/414018492151783883592234375000:ℝ), (585852243442146793386805857631/7811669663241205350796875000:ℝ), (18182137166732350153142368516249/414018492151783883592234375000:ℝ), (567651708853296410480593574057/82803698430356776718446875000:ℝ)],
![(49334551812307360206024308705927/828036984303567767184468750000:ℝ), (112585326145402176791065097338349/828036984303567767184468750000:ℝ), (84561400545100675260045876777517/828036984303567767184468750000:ℝ), (4172809074113586103331117629019/165607396860713553436893750000:ℝ)]]
theorem row179_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (84428186726418006246134730049/15073953278699615886167040000000:ℝ) row179_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row179_coefficients,Fin.sum_univ_succ]
 ring
theorem row179_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row179_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row179_coefficients]
#print axioms row179_identity
#print axioms row179_pos
end
end LewkoStage2Return.C30
