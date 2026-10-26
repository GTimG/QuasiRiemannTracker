/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13796461640966859495358669811/53328906842153044218750000:ℝ),(34097327685644750614902210059/53328906842153044218750000:ℝ),(1392280594196860576186096763/2666445342107652210937500:ℝ),(1873819160118632983700848753/13332226710538261054687500:ℝ)],
![(291490576880062175154041531/740679261696570058593750:ℝ),(121484055256462157005859621/133322267105382610546875:ℝ),(1528773404799748183672211471/2222037785089710175781250:ℝ),(559521455284216726992513571/3333056677634565263671875:ℝ)],
![(544943066898133924901786431/3333056677634565263671875:ℝ),(131394367604345375346153989/370339630848285029296875:ℝ),(820116099688254614585994434/3333056677634565263671875:ℝ),(59004426834841962332464988/1111018892544855087890625:ℝ)]]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14751106708710490583116247/505637042651525160000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row070_coefficients,Fin.sum_univ_succ]
 ring
theorem row070_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row070_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_coefficients]
#print axioms row070_identity
#print axioms row070_pos
end
end LewkoStage1Finite
