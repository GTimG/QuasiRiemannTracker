/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(192028419801073882345867507/741128061181640625000:ℝ),(13940431708965839698313277629/18528201529541015625000:ℝ),(13485104820453353852738284931/18528201529541015625000:ℝ),(4345383606514361213071694977/18528201529541015625000:ℝ)],
![(17317781341782247716608398883/37056403059082031250000:ℝ),(50102737362273031433345637547/37056403059082031250000:ℝ),(12069977670532578425430264499/9264100764770507812500:ℝ),(3873738665409882496245954833/9264100764770507812500:ℝ)],
![(13847213666192427254427549209/65878049882812500000000:ℝ),(7978708604093192880306412741/13175609976562500000000:ℝ),(1196010219187708270789324117/2058689058837890625000:ℝ),(382062426866660234942308039/2058689058837890625000:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (382062426866660234942308039/3837674557440000000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ]
 ring
theorem row040_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
#print axioms row040_identity
#print axioms row040_pos
end
end LewkoStage2Finite
