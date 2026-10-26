/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2101465507304776211716368853783/13332226710538261054687500:ℝ),(5919840438829998560344063597831/13332226710538261054687500:ℝ),(462408965393884882065470213624/1111018892544855087890625:ℝ),(505955082376521321449738032/3898311903666158203125:ℝ)],
![(939568318620973833003029600038/3333056677634565263671875:ℝ),(876558701494355662010364064546/1111018892544855087890625:ℝ),(2447769143562628690471624983712/3333056677634565263671875:ℝ),(757570664169430091916374890112/3333056677634565263671875:ℝ)],
![(272809206022924372659007124/2165728835370087890625:ℝ),(1166519714497718224674574691324/3333056677634565263671875:ℝ),(215439093548144935935622517888/666611335526913052734375:ℝ),(330479652113502276056374861952/3333056677634565263671875:ℝ)]]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2581872282136736531690428609/48541156094546415360000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ]
 ring
theorem row069_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
#print axioms row069_identity
#print axioms row069_pos
end
end LewkoStage1Finite
