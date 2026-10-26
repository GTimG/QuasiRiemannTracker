/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57675644416879366165763763233129/37056403059082031250000:ℝ),(6884036191805636764037747323697/1482256122363281250000:ℝ),(114117930335622803554441682491469/24704268706054687500000:ℝ),(280254988272457542698679525323/182994583007812500000:ℝ)],
![(18643425987083089255232507808337/6176067176513671875000:ℝ),(11124323187396842357587470242387/1235213435302734375000:ℝ),(256081668191578914490520916908/28592903594970703125:ℝ),(203727226438665811080529718317/68622968627929687500:ℝ)],
![(54222229472710771186979916365119/37056403059082031250000:ℝ),(6469630512467229788176950384061/1482256122363281250000:ℝ),(53605645744437548343395799293717/12352134353027343750000:ℝ),(394802991809945714909211515887/274491874511718750000:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (394802991809945714909211515887/4191763996606464000000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
#print axioms row044_identity
#print axioms row044_pos
end
end LewkoStage2Finite
