/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(295293051532145868733879/4444146481595941406250:ℝ), (1553239179126883871363689/8888292963191882812500:ℝ), (333680012265223132581026/2222073240797970703125:ℝ), (124022324332766798809391/2962764321063960937500:ℝ)],
![(1682495034818748844749779/17776585926383765625000:ℝ), (8278330970339558261243741/35553171852767531250000:ℝ), (1650966906004149049958327/8888292963191882812500:ℝ), (13524213786516285024713/284425374822140250000:ℝ)],
![(572429172395700432314263/17776585926383765625000:ℝ), (517113088294213431622307/7110634370553506250000:ℝ), (619780346143927651187339/11851057284255843750000:ℝ), (25834555504790002192438/2222073240797970703125:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12917277752395001096219/63205638849364500000000:ℝ) row001_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ]
 ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
#print axioms row001_identity
#print axioms row001_pos
end
end Record1252270103Return.C30
