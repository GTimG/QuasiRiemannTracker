/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17135889439002646256909271463598812/416632075810783876318359375:ℝ),(16873398000337484862593858204958368/138877358603594625439453125:ℝ),(49838507728590517329802246823383997/416632075810783876318359375:ℝ),(40380710282744935490737693191161/1028721174841441669921875:ℝ)],
![(32252713622743509883844007940633232/416632075810783876318359375:ℝ),(31733072171546183926176693912703088/138877358603594625439453125:ℝ),(31217389518059105950829468659853944/138877358603594625439453125:ℝ),(1228225321053900711981046724783432/16665283032431355052734375:ℝ)],
![(3032286627180711779793926367884984/83326415162156775263671875:ℝ),(993612174581792860387419600911528/9258490573572975029296875:ℝ),(8789376885284853006238940698802552/83326415162156775263671875:ℝ),(2879150505867875552201231283483784/83326415162156775263671875:ℝ)]]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (359893813233484444025153910435473/4970614277977526202531840000000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ]
 ring
theorem row046_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
#print axioms row046_identity
#print axioms row046_pos
end
end LewkoStage2Finite
