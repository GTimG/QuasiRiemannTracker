/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![![(70994392030348822931786060931289/46292452867864875146484375:ℝ),(207247640631847753567941134819561/46292452867864875146484375:ℝ),(8959532445384422638938745236323/2057442349682883339843750:ℝ),(130671689882951622152340028482991/92584905735729750292968750:ℝ)],
![(1144128909132899029391197417702886/416632075810783876318359375:ℝ),(3331072802771883714792709698545354/416632075810783876318359375:ℝ),(43083055128997950862276476986404/5555094344143785017578125:ℝ),(12892314956448966370287529622072/5143605874207208349609375:ℝ)],
![(102166161482737131722972723774587/83326415162156775263671875:ℝ),(296544607444242088005044225095561/83326415162156775263671875:ℝ),(95581836668592501976903561124537/27775471720718925087890625:ℝ),(10262911689320464118047148700293/9258490573572975029296875:ℝ)]]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (10262911689320464118047148700293/138072618832709061181440000000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ]
 ring
theorem row041_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
#print axioms row041_identity
#print axioms row041_pos
end
end LewkoStage2Finite
