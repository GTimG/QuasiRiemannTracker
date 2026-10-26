/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row104_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281014937172666834044102900993/25719127218855631335937500:ℝ),(1951453251595969171221137480531/77157381656566894007812500:ℝ),(358856732311315349453726553184/19289345414141723501953125:ℝ),(6264574566081357173897522792/1483795801087824884765625:ℝ)],
![(154356164147047341482301735706/6429781804713907833984375:ℝ),(1073852146022868251524750057582/19289345414141723501953125:ℝ),(60908360677945768054257596912/1483795801087824884765625:ℝ),(180337428832807581800191409392/19289345414141723501953125:ℝ)],
![(90331845301595030676246769292/6429781804713907833984375:ℝ),(127979093725583953861662185668/3857869082828344700390625:ℝ),(484798779112941097537363066408/19289345414141723501953125:ℝ),(8886445258009115859243649688/1483795801087824884765625:ℝ)]]
theorem row104_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (783071820760169646737190349/345749481315881570304000000000:ℝ) row104_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row104_coefficients,Fin.sum_univ_succ]
 ring
theorem row104_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row104_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row104_coefficients]
#print axioms row104_identity
#print axioms row104_pos
end
end LewkoStage2Finite
