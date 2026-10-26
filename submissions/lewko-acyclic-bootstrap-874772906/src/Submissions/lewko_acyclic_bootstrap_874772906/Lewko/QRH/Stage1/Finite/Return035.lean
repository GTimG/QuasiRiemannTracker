/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2006806805957517374986890653/3555260456143536281250000:ℝ),(15153450277841889223518878671/10665781368430608843750000:ℝ),(630503126963238904015722319/533289068421530442187500:ℝ),(865693231847120821970309917/2666445342107652210937500:ℝ)],
![(113364533135253329897187839/148135852339314011718750:ℝ),(241916985243759490252950181/133322267105382610546875:ℝ),(1877642248811793144632890697/1333222671053826105468750:ℝ),(236999971977912823276539719/666611335526913052734375:ℝ)],
![(53795347428133830600418513/222203778508971017578125:ℝ),(350325228966050853235873609/666611335526913052734375:ℝ),(242764152671342061360096986/666611335526913052734375:ℝ),(52240549111141845050478916/666611335526913052734375:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13060137277785461262619729/303382225590915096000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
#print axioms row035_identity
#print axioms row035_pos
end
end LewkoStage1Finite
