/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14586751518323987287158804967787/277754717207189250878906250:ℝ),(41555400106920153828848562975611/277754717207189250878906250:ℝ),(236503105472797476294397933802791/1666528303243135505273437500:ℝ),(74686919739278614113185167005847/1666528303243135505273437500:ℝ)],
![(11967989512999482611949305920649/138877358603594625439453125:ℝ),(33759726257670586476619370293543/138877358603594625439453125:ℝ),(95067040730722254399155421624292/416632075810783876318359375:ℝ),(5937850795108765009300139451122/83326415162156775263671875:ℝ)],
![(9832759914235990407689639279261/277754717207189250878906250:ℝ),(365360096003471444777285442781/3703396229429190011718750:ℝ),(25386246134467032367012580894717/277754717207189250878906250:ℝ),(7815968239976617312947999465403/277754717207189250878906250:ℝ)]]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7815968239976617312947999465403/129443080155664744857600000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ]
 ring
theorem row061_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
#print axioms row061_identity
#print axioms row061_pos
end
end LewkoStage2Finite
