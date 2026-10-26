/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row204_coefficients : Fin 3 → Fin 4 → ℝ := ![![(332402181572690980293185572442354/10350462303794597089805859375:ℝ), (773101518218381444192013634466662/10350462303794597089805859375:ℝ), (562661165112760448105833822193762/10350462303794597089805859375:ℝ), (40607423984706877219173847139818/3450154101264865696601953125:ℝ)],
![(3920197493389438827588711258127268/51752311518972985449029296875:ℝ), (9266483034234694024607928591442972/51752311518972985449029296875:ℝ), (1384259655737863467429016160315728/10350462303794597089805859375:ℝ), (524492538733873087360512354004312/17250770506324328483009765625:ℝ)],
![(2648421179783779143690716563645798/51752311518972985449029296875:ℝ), (6547979656131708247467996764985062/51752311518972985449029296875:ℝ), (1046368331661004576598097836872061/10350462303794597089805859375:ℝ), (443812955017916732096276486527847/17250770506324328483009765625:ℝ)]]
theorem row204_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (20303711992353438609586923569909/25726213595647344445725081600000000:ℝ) row204_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row204_coefficients,Fin.sum_univ_succ]
 ring
theorem row204_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row204_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row204_coefficients]
#print axioms row204_identity
#print axioms row204_pos
end
end LewkoStage1Return.C30
