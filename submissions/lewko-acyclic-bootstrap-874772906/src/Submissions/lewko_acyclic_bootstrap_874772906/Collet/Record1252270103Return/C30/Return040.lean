/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(614650956452024000632769/2371628742187500000:ℝ), (44620839363492919543073743/59290718554687500000:ℝ), (43163257115723348878081777/59290718554687500000:ℝ), (13908691663531029350827259/59290718554687500000:ℝ)],
![(55428387201473445166545361/118581437109375000000:ℝ), (160361213623008431885937449/118581437109375000000:ℝ), (38631547727547278410172033/29645359277343750000:ℝ), (12398341122163531730324011/29645359277343750000:ℝ)],
![(44317494608464936880921603/210811443750000000000:ℝ), (76606178363611032633457141/126486866250000000000:ℝ), (11483202566120335118286917/19763572851562500000:ℝ), (3668252316349699101895639/19763572851562500000:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3668252316349699101895639/36841970073600000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Return.C30
