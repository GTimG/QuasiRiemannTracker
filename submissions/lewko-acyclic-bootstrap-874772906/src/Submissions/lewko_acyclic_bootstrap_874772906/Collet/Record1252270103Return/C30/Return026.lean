/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![![(263082677433883534724182897/2222073240797970703125:ℝ), (750444875606081717123203441/2222073240797970703125:ℝ), (158371680981902946338095223/493794053510660156250:ℝ), (150201409733331429263896973/1481382160531980468750:ℝ)],
![(419543444866461065410873238/2222073240797970703125:ℝ), (1185562675203496099999388666/2222073240797970703125:ℝ), (1114684693242430086548637368/2222073240797970703125:ℝ), (69729131790822402923274388/444414648159594140625:ℝ)],
![(162836521571902669161771991/2222073240797970703125:ℝ), (18178691327615477520970021/88882929631918828125:ℝ), (421568197055258550937659527/2222073240797970703125:ℝ), (129925553066004459668930993/2222073240797970703125:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (129925553066004459668930993/1035561186907987968000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ]
 ring
theorem row026_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
#print axioms row026_identity
#print axioms row026_pos
end
end Record1252270103Return.C30
