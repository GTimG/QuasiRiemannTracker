/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row140_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1115983102452068755630161151/23318675631924786281250000:ℝ),(17756208162416386847603089459/209868080687323076531250000:ℝ),(4506883670713716540146471293/104934040343661538265625000:ℝ),(523183832527833475868151743/104934040343661538265625000:ℝ)],
![(790807171196422166801887283/5829668907981196570312500:ℝ),(13099013935061867522885437583/52467020171830769132812500:ℝ),(1442751138356434597681534181/10493404034366153826562500:ℝ),(1061980006805439578989218869/52467020171830769132812500:ℝ)],
![(1270288015047423085558608353/11659337815962393140625000:ℝ),(23021706628951690898484593339/104934040343661538265625000:ℝ),(14829787561920730532897554387/104934040343661538265625000:ℝ),(6345202836811846078821971/220913769144550606875000:ℝ)]]
theorem row140_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (523183832527833475868151743/191026590776727849216000000000:ℝ) row140_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row140_coefficients,Fin.sum_univ_succ]
 ring
theorem row140_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row140_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row140_coefficients]
#print axioms row140_identity
#print axioms row140_pos
end
end LewkoStage1Finite
