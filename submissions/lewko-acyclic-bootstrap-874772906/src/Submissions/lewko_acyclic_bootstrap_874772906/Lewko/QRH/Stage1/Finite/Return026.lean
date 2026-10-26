/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![![(157898612574081201076413914387/1333222671053826105468750:ℝ),(450406813327517748632761943411/1333222671053826105468750:ℝ),(855472841986782514449702984197/2666445342107652210937500:ℝ),(270446537874418476494038176149/2666445342107652210937500:ℝ)],
![(125908524013211011507867523489/666611335526913052734375:ℝ),(355798062075185740462120160783/666611335526913052734375:ℝ),(334527592688213247203234530924/666611335526913052734375:ℝ),(20926422612588790508640128726/133322267105382610546875:ℝ)],
![(97743854435855555376838350101/1333222671053826105468750:ℝ),(10911956115500321232865183679/53328906842153044218750:ℝ),(253052309686125834447436543477/1333222671053826105468750:ℝ),(77990131358519880155707801603/1333222671053826105468750:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (77990131358519880155707801603/621326798010194116608000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ]
 ring
theorem row026_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
#print axioms row026_identity
#print axioms row026_pos
end
end LewkoStage1Finite
