/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1724557643564981657514807619717/6666113212972542021093750000:ℝ),(473573974910938652495728002797/740679245885838002343750000:ℝ),(6445743164588527803207439193/12344654098097300039062500:ℝ),(234227381862014044509599439691/1666528303243135505273437500:ℝ)],
![(36436319469456690361953680807/92584905735729750292968750:ℝ),(15185505546985798005901712627/16665283032431355052734375:ℝ),(573289965233943442119888698461/833264151621567752636718750:ℝ),(23313391029611591361126865729/138877358603594625439453125:ℝ)],
![(68117875550130766281216630857/416632075810783876318359375:ℝ),(147818642347441910971387757447/416632075810783876318359375:ℝ),(102514494276526128261510614798/416632075810783876318359375:ℝ),(22126655168516914599464488208/416632075810783876318359375:ℝ)]]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1382915948032307162466530513/47403471736693632150000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage2Finite
